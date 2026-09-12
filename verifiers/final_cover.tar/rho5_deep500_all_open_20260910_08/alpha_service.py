"""Persistent X alpha sidecar. A 600s check cadence never interrupts search."""
from pathlib import Path
from collections import OrderedDict, Counter
import argparse
import os
import signal
import time
import traceback
import alpha_scanner as asc

PAID = {'CLOSED', 'COVERED_BY_PRODUCTION', 'COVERED_BY_ALPHA'}
INTERVAL = 600


class BoundedCache(OrderedDict):
    def __init__(self, limit):
        super().__init__()
        self.limit = limit

    def __setitem__(self, key, value):
        super().__setitem__(key, value)
        self.move_to_end(key)
        while len(self) > self.limit:
            self.popitem(last=False)

    def get(self, key, default=None):
        if key not in self:
            return default
        self.move_to_end(key)
        return super().get(key)


class StopSidecar(asc.BudgetExpired):
    pass


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, default=asc.DEFAULT_ROOT)
    ap.add_argument('--b14-dir', type=Path, required=True)
    args = ap.parse_args()
    args.seconds = 1200
    os.nice(max(0, 10 - os.getpriority(os.PRIO_PROCESS, 0)))
    s = asc.Scanner(args)  # Holds SCANNER.lock for this process's lifetime.
    for name, limit in [('discovery_prefix', 16), ('discovery_nodes', 8192),
                        ('discovery_ports', 8192), ('verifier_cache', 8192)]:
        setattr(s, name, BoundedCache(limit))
    state_path = s.out / 'ALPHA_SERVICE_STATE.json'
    state = asc.read(state_path) if state_path.exists() else {'schema': 'RHO5_ALPHA_SIDECAR_V1', 'tasks': {}}
    if state.get('schema') != 'RHO5_ALPHA_SIDECAR_V1':
        raise ValueError('Wrong alpha sidecar state schema')
    stopping = False
    current_task = None
    last_task_check = 0.0
    original_safe_point = s.safe_point

    def stop_requested():
        return stopping or (s.root / 'STOP.json').exists() or (s.out / 'STOP_SCANNER.json').exists()

    def safe_point():
        nonlocal last_task_check
        if stop_requested():
            raise StopSidecar('User/root requested sidecar stop')
        if current_task and time.monotonic() - last_task_check >= 5:
            last_task_check = time.monotonic()
            row = asc.read(s.root / 'RUN_STATE.json')['tasks'].get(current_task)
            if not row or row.get('status') != 'RUNNING':
                raise StopSidecar('Owned task is no longer RUNNING; skip this scan')
        original_safe_point()

    def sig_stop(signum, frame):
        nonlocal stopping
        stopping = True
        if current_task:
            raise StopSidecar('Sidecar signal; search receives no signal')

    def sig_budget(signum, frame):
        raise asc.BudgetExpired('1200-second sidecar scan budget; search unchanged')

    def status(phase):
        state['updated_epoch'] = time.time()
        asc.atomic(state_path, state)
        asc.atomic(s.out / 'ALPHA_SERVICE_STATUS.json', {'schema': state['schema'], 'phase': phase,
            'epoch': time.time(), 'pid': os.getpid(), 'current_task': current_task,
            'check_interval_seconds': INTERVAL, 'per_scan_budget_seconds': 1200,
            'model_wakeups': False, 'search_signals_sent': False,
            'cache_sizes': {n: len(getattr(s, n)) for n in ('discovery_prefix', 'discovery_nodes', 'discovery_ports', 'verifier_cache')}})

    s.safe_point = safe_point
    signal.signal(signal.SIGTERM, sig_stop)
    signal.signal(signal.SIGINT, sig_stop)
    signal.signal(signal.SIGALRM, sig_budget)
    phase = 'STOPPED'
    try:
        while not stop_requested():
            tasks = asc.read(s.root / 'RUN_STATE.json')['tasks']
            if tasks and all(t.get('status') in PAID for t in tasks.values()):
                phase = 'ALL_ORIGINAL_TASKS_PAID'
                break
            for key, row in sorted(tasks.items()):
                if stop_requested():
                    break
                previous = state['tasks'].get(key, {})
                if row.get('status') != 'RUNNING' or time.time() - previous.get('last_check_epoch', 0) < INTERVAL:
                    continue
                path = s.owned(row['folder']) / 'final.json'
                if not path.exists():
                    state['tasks'][key] = {**previous, 'last_check_epoch': time.time(), 'phase': 'AWAITING_FIRST_ATOMIC_CHECKPOINT'}
                    continue
                st = path.stat()
                fingerprint = [st.st_ino, st.st_size, st.st_mtime_ns]
                stamp = {**previous, 'last_check_epoch': time.time(), 'observed_fingerprint': fingerprint}
                state['tasks'][key] = stamp
                if fingerprint == previous.get('observed_fingerprint'):
                    stamp['phase'] = 'UNCHANGED_FILE_SKIPPED'
                    continue
                current_task = key
                s.run_id = 'service_' + str(time.time_ns()) + '_' + str(os.getpid())
                s.run_dir = s.out / 'runs' / s.run_id
                s.run_dir.mkdir(parents=True)
                s.started, s.started_cpu = time.monotonic(), time.process_time()
                s.counter, s.diag_counts = Counter(), Counter()
                s.current = s.current_reduced = s.current_certificate = None
                stamp['phase'] = 'SCANNING'
                status('SCANNING')
                signal.setitimer(signal.ITIMER_REAL, 1200)
                try:
                    s.safe_point()
                    source = s.running_source(row)
                    identity = source[3]['source_file_sha256']
                    stamp['source_file_sha256'] = identity
                    if identity == previous.get('source_file_sha256'):
                        stamp['phase'] = 'UNCHANGED_BYTES_SKIPPED'
                    else:
                        s.scan(*source)
                        stamp.update(phase='COMPLETED', run_id=s.run_id, completed_epoch=time.time())
                except asc.BudgetExpired as exc:
                    stamp.update(phase='SCAN_STOPPED_PARTIAL_SAVED', reason=str(exc), run_id=s.run_id)
                    signal.setitimer(signal.ITIMER_REAL, 0)
                    s.save_partial(stamp['phase'])
                    s.event('SIDECAR_SCAN_STOP', reason=str(exc))
                finally:
                    signal.setitimer(signal.ITIMER_REAL, 0)
                    current_task = None
                    status('WAITING_FOR_CHANGED_CHECKPOINT')
                    s.progress(stamp['phase'], force=True)
            status('WAITING_FOR_CHANGED_CHECKPOINT')
            for _ in range(5):
                if stop_requested():
                    break
                time.sleep(1)
    except BaseException:
        signal.setitimer(signal.ITIMER_REAL, 0)
        phase = 'ERROR_SAVED_NO_AUTOMATIC_RETRY'
        asc.atomic(s.out / 'ALPHA_SERVICE_ERROR.json', {'epoch': time.time(), 'error': traceback.format_exc(), 'current_task': current_task})
        s.failed_source('ALPHA_SERVICE')
        s.save_partial(phase)
        return 2
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        status(phase)
        s.progress(phase, force=True)
        s.lock.close()
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
