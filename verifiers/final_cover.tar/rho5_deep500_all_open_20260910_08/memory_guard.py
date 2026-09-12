"""Independent checkpoint-preserving memory guard for this one X search root.

No mathematics, worker restart, RUN_STATE write, group signals, or /proc sweep.
The coordinator owns retry after memory has remained available for 60 seconds.
"""
from pathlib import Path
import fcntl
import ctypes
import json
import os
import signal
import sys
import time
import traceback
import uuid

ROOT = Path(__file__).resolve().parent
GiB = 1024 ** 3
LOW = 8 * GiB
CRITICAL = 4 * GiB
RECOVER = 12 * GiB
POLL_SECONDS = 2
SELECT_INTERVAL = 8
COOPERATIVE_GRACE = 30


def _pidfd_syscall(number, *args):
    """Compatibility for this X kernel when CPython omitted pidfd bindings."""
    if sys.platform != 'linux' or os.uname().machine != 'x86_64':
        raise RuntimeError('pidfd syscall compatibility is restricted to Linux x86_64')
    libc = ctypes.CDLL(None, use_errno=True)
    libc.syscall.restype = ctypes.c_long
    ctypes.set_errno(0)
    result = libc.syscall(ctypes.c_long(number), *args)
    if result == -1:
        code = ctypes.get_errno()
        raise OSError(code, os.strerror(code))
    return int(result)


def pidfd_open_compat(pid):
    native = getattr(os, 'pidfd_open', None)
    if callable(native):
        return native(int(pid), 0)
    # Linux x86_64 __NR_pidfd_open, verified against X's kernel headers.
    return _pidfd_syscall(434, ctypes.c_int(int(pid)), ctypes.c_uint(0))


def pidfd_send_signal_compat(fd, sig):
    native = getattr(signal, 'pidfd_send_signal', None)
    if callable(native):
        return native(int(fd), int(sig), None, 0)
    # Linux x86_64 __NR_pidfd_send_signal; NULL siginfo and zero flags.
    return _pidfd_syscall(424, ctypes.c_int(int(fd)), ctypes.c_int(int(sig)),
                          ctypes.c_void_p(None), ctypes.c_uint(0))


def probe_pidfd_support():
    """No-signal deployment probe: open and close our own process descriptor."""
    fd = pidfd_open_compat(os.getpid())
    try:
        return {'status': 'SELF_PIDFD_OPENED', 'pid': os.getpid(), 'signal_sent': False,
                'open_backend': 'python' if callable(getattr(os, 'pidfd_open', None)) else 'libc_syscall_434',
                'send_backend': 'python' if callable(getattr(signal, 'pidfd_send_signal', None)) else 'libc_syscall_424'}
    finally:
        os.close(fd)


def read_json(path):
    return json.loads(Path(path).read_text())


def atomic_json(path, data):
    path = Path(path)
    tmp = path.with_name(path.name + '.tmp.' + str(os.getpid()))
    try:
        with tmp.open('w') as f:
            json.dump(data, f, sort_keys=True, separators=(',', ':'))
            f.write('\n')
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    finally:
        if tmp.exists():
            tmp.unlink()


def exclusive_json(path, data):
    try:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError:
        return False
    with os.fdopen(fd, 'w') as f:
        json.dump(data, f, sort_keys=True, separators=(',', ':'))
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    return True


class Linux:
    def process_info(self, pid):
        try:
            p = Path('/proc') / str(int(pid))
            tail = (p / 'stat').read_text().rsplit(')', 1)[1].split()
            return {'pid': int(pid), 'start_ticks': tail[19], 'state': tail[0],
                    'ppid': int(tail[1]),
                    'args': [v.decode() for v in (p / 'cmdline').read_bytes().split(b'\0') if v]}
        except (OSError, ValueError, IndexError):
            return None

    def memory_available(self):
        for line in Path('/proc/meminfo').read_text().splitlines():
            if line.startswith('MemAvailable:'):
                return int(line.split()[1]) * 1024
        raise RuntimeError('MemAvailable is unavailable')

    def children(self, pid):
        try:
            p = Path('/proc') / str(pid) / 'task' / str(pid) / 'children'
            return [int(v) for v in p.read_text().split()]
        except FileNotFoundError:
            return []

    def kill_exact(self, identity):
        """pidfd binds the signal to a process even if the numeric PID is reused."""
        current = self.process_info(identity['pid'])
        if not same_process(current, identity):
            return False
        try:
            fd = pidfd_open_compat(identity['pid'])
        except ProcessLookupError:
            return False
        try:
            if not same_process(self.process_info(identity['pid']), identity):
                return False
            try:
                pidfd_send_signal_compat(fd, signal.SIGKILL)
                return True
            except ProcessLookupError:
                return False
        finally:
            os.close(fd)


def same_process(current, expected):
    return bool(current and current.get('state') not in ('Z', 'X')
                and current['pid'] == expected['pid']
                and str(current['start_ticks']) == str(expected['start_ticks'])
                and current['args'] == expected['args'])


class MemoryGuard:
    def __init__(self, root=ROOT, backend=None, clock=time.time):
        self.root = Path(root).resolve()
        self.backend = backend or Linux()
        self.clock = clock
        self.last_selection = 0.0
        self.stable_since = None
        self.pauses = {}
        me = self.backend.process_info(os.getpid())
        self.identity = {'pid': os.getpid(), 'start_ticks': me['start_ticks'] if me else None}
        self.recovered = False

    def event(self, event, **data):
        with (self.root / 'MEMORY_GUARD_EVENTS.jsonl').open('a') as f:
            f.write(json.dumps({'epoch': self.clock(), 'event': event, **data},
                               sort_keys=True, separators=(',', ':')) + '\n')
            f.flush()

    def folder(self, task_id, row):
        if row.get('task_id') != task_id or not isinstance(task_id, str):
            return None
        folder = (self.root / str(row.get('folder', ''))).resolve()
        expected = self.root / 'tasks' / task_id
        if expected.parent != self.root / 'tasks' or folder != expected:
            return None
        return folder

    def identity_for(self, row, folder):
        entry = str(self.root / 'branch_worker.py')
        if row.get('entrypoint') != entry:
            return None
        current = self.backend.process_info(row.get('pid', -1))
        if (not current or current['state'] in ('Z', 'X')
                or str(current['start_ticks']) != str(row.get('start_ticks'))):
            return None
        args = current['args']
        if entry not in args:
            return None
        at = args.index(entry)
        if at + 1 >= len(args) or args[at + 1] != str(folder):
            return None
        return current

    def owned_pause(self, folder, record):
        try:
            pause = read_json(folder / 'MEMORY_PAUSE.json')
            stop = read_json(folder / 'STOP.json')
            return (pause.get('token') == record.get('token') == stop.get('token')
                    and pause.get('reason') == stop.get('reason') == 'MEMORY_PRESSURE_PAUSE'
                    and pause.get('pid') == record.get('pid') == stop.get('pid')
                    and str(pause.get('start_ticks')) == str(record.get('start_ticks'))
                    == str(stop.get('start_ticks')))
        except FileNotFoundError:
            return False

    def recover_pauses(self, state):
        for task_id, row in state['tasks'].items():
            folder = self.folder(task_id, row)
            if not folder or not (folder / 'MEMORY_PAUSE.json').exists():
                continue
            record = read_json(folder / 'MEMORY_PAUSE.json')
            if record.get('automatic_retry') is True and self.owned_pause(folder, record):
                self.pauses[task_id] = record
                self.last_selection = max(self.last_selection, float(record['epoch']))
        self.recovered = True

    def checkpoint_exists(self, folder):
        final = folder / 'final.json'
        return (final.is_file() and not final.is_symlink() and final.stat().st_size > 0
                and not (folder / 'ERROR.json').exists() and not (folder / 'RESULT.json').exists())

    def pause(self, task_id, row, folder, available, emergency):
        if (self.root / 'STOP.json').exists() or (folder / 'STOP.json').exists():
            return False
        identity = self.identity_for(row, folder)
        if not identity or not self.checkpoint_exists(folder):
            return False
        token = uuid.uuid4().hex
        final = (folder / 'final.json').stat()
        record = {'token': token, 'episode_token': token, 'epoch': self.clock(),
                  'pid': identity['pid'], 'start_ticks': identity['start_ticks'],
                  'task_id': task_id, 'folder': row['folder'], 'entrypoint': row['entrypoint'],
                  'started_epoch': row.get('started_epoch'), 'reason': 'MEMORY_PRESSURE_PAUSE',
                  'automatic_retry': True, 'forced': False,
                  'emergency_old_worker': emergency, 'memory_available_bytes': available,
                  'checkpoint_file': 'final.json', 'checkpoint_size_bytes': final.st_size,
                  'checkpoint_mtime_ns': final.st_mtime_ns,
                  'cooperative_grace_seconds': COOPERATIVE_GRACE}
        if not exclusive_json(folder / 'MEMORY_PAUSE.json', record):
            return False
        # Recheck after writing the ownership record, before asking the worker to stop.
        if (self.root / 'STOP.json').exists() or not self.identity_for(row, folder):
            record.update(automatic_retry=False, action_status='ABORTED_BEFORE_STOP')
            atomic_json(folder / 'MEMORY_PAUSE.json', record)
            return False
        if not exclusive_json(folder / 'STOP.json', record):
            record.update(automatic_retry=False, action_status='EXISTING_STOP_PRESERVED')
            atomic_json(folder / 'MEMORY_PAUSE.json', record)
            self.event('STOP_CONFLICT_PRESERVED', task_id=task_id, token=token)
            return False
        self.pauses[task_id] = record
        self.last_selection = record['epoch']
        self.event('COOPERATIVE_MEMORY_PAUSE', **record)
        return True

    def force_expired(self, state, available):
        forced_any = False
        for task_id, record in list(self.pauses.items()):
            row = state['tasks'].get(task_id)
            folder = self.folder(task_id, row) if row else None
            if not folder or not self.owned_pause(folder, record):
                self.pauses.pop(task_id, None)
                continue
            if (row.get('status') != 'RUNNING' or row.get('pid') != record.get('pid')
                    or str(row.get('start_ticks')) != str(record.get('start_ticks'))):
                continue
            identity = self.identity_for(record, folder)
            if not identity:
                continue
            if (available >= CRITICAL or self.clock() - record['epoch'] < COOPERATIVE_GRACE
                    or record.get('forced') or not self.checkpoint_exists(folder)):
                continue
            if (self.root / 'STOP.json').exists():
                return forced_any
            helpers = []
            helper_entry = str(self.root / 'lp_guard.py')
            for child in self.backend.children(identity['pid']):
                helper = self.backend.process_info(child)
                if not helper or helper['ppid'] != identity['pid'] or helper_entry not in helper['args']:
                    continue
                args = helper['args']; at = args.index(helper_entry)
                if args[at + 1:at + 3] == ['--server', str(folder / 'lp_guard')]:
                    helpers.append(helper)
            # Coordinator cannot resume a live matching PID. Persist intent before SIGKILL.
            record.update(forced=True, forced_epoch=self.clock(),
                          forced_reason='Below 4 GiB after 30-second checkpoint-preserving cooperative grace',
                          forced_processes=[{'pid': p['pid'], 'start_ticks': p['start_ticks']}
                                            for p in helpers + [identity]])
            atomic_json(folder / 'MEMORY_PAUSE.json', record)
            signals = []
            for owned in helpers + [identity]:
                if (self.root / 'STOP.json').exists():
                    break
                if not self.owned_pause(folder, record) or not self.checkpoint_exists(folder):
                    break
                if self.backend.kill_exact(owned):
                    signals.append(owned['pid'])
            record['signalled_pids'] = signals
            atomic_json(folder / 'MEMORY_PAUSE.json', record)
            self.event('FORCED_MEMORY_PAUSE', task_id=task_id, token=record['token'],
                       signalled_pids=signals, emergency_old_worker=record['emergency_old_worker'])
            forced_any = True
        return forced_any

    def select(self, state, config, available):
        if available >= LOW or self.clock() - self.last_selection < SELECT_INTERVAL:
            return
        deployment = float(config['memory_policy_deployed_epoch'])
        candidates = []
        for task_id, row in state['tasks'].items():
            if row.get('status') != 'RUNNING':
                continue
            folder = self.folder(task_id, row)
            if (not folder or (folder / 'STOP.json').exists()
                    or (folder / 'MEMORY_PAUSE.json').exists()
                    or not self.checkpoint_exists(folder) or not self.identity_for(row, folder)):
                continue
            began = row.get('started_epoch')
            if not isinstance(began, (float, int)):
                continue
            candidates.append((began >= deployment, began, task_id, row, folder))
        new = [v for v in candidates if v[0]]
        if new:
            _, _, task_id, row, folder = max(new, key=lambda v: (v[1], v[2]))
            self.pause(task_id, row, folder, available, False)
            return
        if available >= CRITICAL:
            return
        # Give a newly requested pause its full grace before touching pre-upgrade work.
        for task_id, record in self.pauses.items():
            if self.clock() - record['epoch'] >= COOPERATIVE_GRACE:
                continue
            row = state['tasks'].get(task_id)
            folder = self.folder(task_id, row) if row else None
            if folder and self.identity_for(record, folder):
                return
        if candidates:
            _, _, task_id, row, folder = max(candidates, key=lambda v: (v[1], v[2]))
            self.pause(task_id, row, folder, available, True)

    def step(self):
        now = self.clock()
        available = self.backend.memory_available()
        config = read_json(self.root / 'CONFIG.json')
        if available >= RECOVER:
            if self.stable_since is None:
                self.stable_since = now
        else:
            self.stable_since = None
        globally_stopped = (self.root / 'STOP.json').exists()
        if config.get('memory_guard_enabled') is True and not globally_stopped:
            state = read_json(self.root / 'RUN_STATE.json')
            if not isinstance(state.get('tasks'), dict):
                raise ValueError('RUN_STATE.tasks is not a mapping')
            if not self.recovered:
                self.recover_pauses(state)
            if not self.force_expired(state, available):
                self.select(state, config, available)
        status = {'epoch': now, **self.identity, 'memory_available_bytes': available,
                  'phase': 'LOW_MEMORY' if available < LOW else 'HEALTHY',
                  'stable_available_since': self.stable_since,
                  'enabled': config.get('memory_guard_enabled') is True,
                  'global_stop': globally_stopped, 'last_pause_epoch': self.last_selection,
                  'automatic_retry_owner': 'coordinator'}
        atomic_json(self.root / 'MEMORY_GUARD_STATUS.json', status)
        return status

    def fail(self, error):
        failure = {'epoch': self.clock(), **self.identity, 'phase': 'ERROR',
                   'error': str(error), 'traceback': traceback.format_exc(),
                   'stable_available_since': None, 'automatic_retry': False}
        try:
            failure['memory_available_bytes'] = self.backend.memory_available()
        except Exception:
            failure['memory_available_bytes'] = None
        if not (self.root / 'GUARD_ERROR.json').exists():
            exclusive_json(self.root / 'GUARD_ERROR.json', failure)
        atomic_json(self.root / 'MEMORY_GUARD_STATUS.json', failure)


def main():
    os.nice(max(0, 10 - os.getpriority(os.PRIO_PROCESS, 0)))
    with (ROOT / 'MEMORY_GUARD.lock').open('a+') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return 0
        guard = MemoryGuard()
        try:
            if (ROOT / 'GUARD_ERROR.json').exists():
                raise RuntimeError('Existing GUARD_ERROR.json requires explicit inspection before restart')
            while True:
                before = time.monotonic()
                status = guard.step()
                if status['global_stop']:
                    return 0
                time.sleep(max(0.0, POLL_SECONDS - (time.monotonic() - before)))
        except Exception as exc:
            guard.fail(exc)
            return 1


if __name__ == '__main__':
    raise SystemExit(main())
