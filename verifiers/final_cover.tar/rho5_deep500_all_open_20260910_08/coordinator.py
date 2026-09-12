"""Durable X-only per-original-OPEN scheduler; no search time slices or model calls."""
from pathlib import Path
from collections import Counter
import fcntl
import hashlib
import json
import os
import signal
import shutil
import subprocess
import sys
import time
import traceback
sys.setrecursionlimit(10000)
sys.dont_write_bytecode = True
for k in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[k] = '1'
ROOT = Path(__file__).resolve().parent
from fast_checkpoint import atomic_json
from source_inputs import Inputs, read
from resource_capacity import capacity_sample
import deep_math as dm


def process_info(pid):
    try:
        p = Path('/proc') / str(pid)
        tail = (p / 'stat').read_text().rsplit(')', 1)[1].split()
        args = (p / 'cmdline').read_bytes().split(b'\0')
        return {'start_ticks': tail[19], 'state': tail[0],
                'args': [x.decode() for x in args if x]}
    except (OSError, ValueError, IndexError):
        return None


def alive(row):
    p = process_info(row.get('pid', -1))
    return bool(p and p['state'] not in ('Z', 'X') and str(row.get('start_ticks')) == p['start_ticks']
                and row.get('entrypoint') in p['args'])


def memory_episode_token(record):
    """Accept the guard's episode name without accepting conflicting aliases."""
    if not isinstance(record, dict):
        return None
    token = record.get('token', record.get('episode_token'))
    if ('token' in record and 'episode_token' in record
            and record['token'] != record['episode_token']):
        return None
    return token


class Coordinator:
    def __init__(self):
        self.config = read(ROOT / 'CONFIG.json')
        self.inputs = Inputs(ROOT, self.config)
        self.state = read(ROOT / 'RUN_STATE.json') if (ROOT / 'RUN_STATE.json').exists() else {
            'schema': 'RHO5_ALL_OPEN_BRANCH_DEPTH500_RUN_V1', 'tasks': {}, 'parents': {},
            'mergers': {}, 'started_epoch': time.time(), 'source_root': self.config['source_root']}
        self.children = {}
        self.last_discover = 0
        self.last_capacity = {}
        self.last_status = 0
        self.stop_signal = False
        (ROOT / 'tmp').mkdir(exist_ok=True)
        self.event('COORDINATOR_STARTED', pid=os.getpid())
        self.recover()
        self.alpha_bridge = None
        try:
            from alpha_bridge import AlphaBridge
            self.alpha_bridge = AlphaBridge(ROOT, self, alive)
        except Exception:
            atomic_json(ROOT / 'ALPHA_BRIDGE_INIT_ERROR.json',
                        {'epoch': time.time(), 'error': traceback.format_exc(),
                         'old_searches_preserved': True})
            self.event('ALPHA_BRIDGE_INIT_ERROR', error=traceback.format_exc())
        self.ensure_memory_guard()

    def ensure_memory_guard(self):
        if not self.config.get('memory_guard_enabled'):
            return
        if (ROOT / 'GUARD_ERROR.json').exists():
            self.event('MEMORY_GUARD_ERROR_ADMISSION_BLOCKED')
            return
        entry = str(ROOT / 'memory_guard.py')
        # Guard survives a coordinator replacement, so adopt by script identity.
        for proc in Path('/proc').iterdir():
            if proc.name.isdigit():
                info = process_info(proc.name)
                if info and info['state'] not in ('Z', 'X') and entry in info['args']:
                    self.event('MEMORY_GUARD_ADOPTED', pid=int(proc.name))
                    return
        with (ROOT / 'MEMORY_GUARD.log').open('ab') as log:
            child = subprocess.Popen([sys.executable, '-B', entry], cwd=ROOT,
                stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
                start_new_session=True, env=dict(os.environ))
        self.event('MEMORY_GUARD_STARTED', pid=child.pid)

    def memory_guard_status(self):
        if not self.config.get('memory_guard_enabled'):
            if self.config.get('memory_admission_mode') == 'actual_rss_incremental':
                return {'healthy': False, 'reason': 'Dynamic memory admission requires the independent guard'}
            return {'healthy': True, 'stable_available_since': 0}
        try:
            status = read(ROOT / 'MEMORY_GUARD_STATUS.json')
            info = process_info(status['pid'])
            healthy = bool(info and info['state'] not in ('Z', 'X', 'T', 't')
                and info['start_ticks'] == str(status['start_ticks'])
                and str(ROOT / 'memory_guard.py') in info['args']
                and 0 <= time.time() - status['epoch'] <= 10
                and status.get('phase') == 'HEALTHY'
                and not (ROOT / 'GUARD_ERROR.json').exists())
            return {**status, 'healthy': healthy}
        except (OSError, ValueError, KeyError, TypeError):
            return {'healthy': False, 'reason': 'Guard heartbeat missing or invalid'}

    def memory_pause_record(self, task):
        folder = ROOT / task['folder']
        try:
            pause_path = folder / 'MEMORY_PAUSE.json'
            resume_token = task.get('memory_resume_token')
            if (not pause_path.exists() and task.get('memory_resume_inflight')
                    and isinstance(resume_token, str) and resume_token
                    and all(c in '0123456789abcdef-' for c in resume_token)):
                pause_path = folder / 'memory_pauses' / resume_token / 'MEMORY_PAUSE.json'
            record = read(pause_path)
            stop = read(folder / 'STOP.json') if (folder / 'STOP.json').exists() else None
            token = memory_episode_token(record)
            matches = (record.get('reason') == 'MEMORY_PRESSURE_PAUSE'
                and record.get('task_id') == task['task_id']
                and record.get('automatic_retry') is True
                and bool(token)
                and record.get('pid') == task.get('pid')
                and str(record.get('start_ticks')) == str(task.get('start_ticks')))
            # STOP is absent only after our durable resume intent was recorded.
            owns_stop = (stop and memory_episode_token(stop) == token
                         and stop.get('reason') == 'MEMORY_PRESSURE_PAUSE')
            resuming = task.get('memory_resume_token') == token
            if matches and (owns_stop or (stop is None and resuming)):
                return {**record, 'token': token}
        except (OSError, ValueError, KeyError, TypeError):
            pass
        return None

    def resume_memory_task(self, task):
        folder = ROOT / task['folder']
        record = self.memory_pause_record(task)
        if (not record or alive(task) or self.stop_signal or (ROOT / 'STOP.json').exists()
                or any((folder / name).exists() for name in ('RESULT.json', 'ERROR.json'))
                or not (folder / 'final.json').is_file()):
            return False
        request = read(folder / 'TASK.json')
        if any(request.get(k) != task.get(k) for k in ('task_id', 'index', 'target_path', 'input_sha256')):
            raise ValueError('Memory resume immutable task binding mismatch')
        token = record['token']
        if not isinstance(token, str) or not token or any(c not in '0123456789abcdef-' for c in token):
            raise ValueError('Invalid memory pause token')
        archive = folder / 'memory_pauses' / token
        archive.mkdir(parents=True, exist_ok=True)
        # Persist intent before releasing the guard-owned STOP. If interrupted,
        # recover/harvest can return this same immutable task to the resume queue.
        task.update(memory_resume_token=token, memory_resume_inflight=True,
                    status='MEMORY_PRESSURE_PAUSED')
        self.save()
        for name in ('MEMORY_PAUSE.json', 'STOP.json', 'STOPPED.json'):
            source = folder / name
            if source.exists():
                if name == 'STOP.json':
                    current_stop = read(source)
                    if (memory_episode_token(current_stop) != token
                            or current_stop.get('reason') != 'MEMORY_PRESSURE_PAUSE'):
                        return False
                shutil.copy2(source, archive / name)
        stop = folder / 'STOP.json'
        if stop.exists():
            current_stop = read(stop)
            if (memory_episode_token(current_stop) != token
                    or current_stop.get('reason') != 'MEMORY_PRESSURE_PAUSE'):
                return False
            stop.unlink()
        stopped = folder / 'STOPPED.json'
        if stopped.exists():
            stopped.unlink()
        pause_path = folder / 'MEMORY_PAUSE.json'
        if pause_path.exists():
            if memory_episode_token(read(pause_path)) != token:
                return False
            # The independent guard creates this record with O_EXCL. Release
            # the old episode BEFORE spawn, retaining a durable intent pointing
            # at its archive in case this coordinator is interrupted here.
            os.replace(pause_path, archive / 'MEMORY_PAUSE.json')
        atomic_json(archive / 'RESUME.json', {'epoch': time.time(), 'task_id': task['task_id'],
            'from_checkpoint': str(folder / 'final.json'), 'same_input_sha256': request['input_sha256'],
            'mathematical_acceptance': 'NOT_CLAIMED'})
        # A user stop can arrive while audit files are copied. Do not spawn after
        # it, even though the worker would subsequently observe the same stop.
        if self.stop_signal or (ROOT / 'STOP.json').exists() or (folder / 'STOP.json').exists():
            return False
        task['status'] = 'STARTING'
        self.save()
        task.update(self.start_child('branch_worker.py', [str(folder)], folder / 'WORKER.log'))
        task['memory_resume_inflight'] = False
        task['memory_resume_count'] = task.get('memory_resume_count', 0) + 1
        task['last_memory_resume_epoch'] = time.time()
        self.save()
        # Do not unlink any pause records here: the independent guard may already
        # have created a NEW episode for this new PID after the RUNNING save.
        self.event('MEMORY_CHECKPOINT_RESUMED', task_id=task['task_id'], pid=task['pid'],
                   token=token, input_sha256=request['input_sha256'])
        return True

    def event(self, kind, **data):
        with (ROOT / 'EVENTS.jsonl').open('a') as f:
            f.write(json.dumps({'epoch': time.time(), 'event': kind, **data}, sort_keys=True) + '\n')
            f.flush()

    def save(self):
        self.state['updated_epoch'] = time.time()
        atomic_json(ROOT / 'RUN_STATE.json', self.state)

    def recover(self):
        # Adopt children spawned just before an interrupted coordinator state write.
        folders = {str((ROOT / t['folder']).resolve()): t for t in self.state['tasks'].values()}
        for proc in Path('/proc').iterdir():
            if not proc.name.isdigit():
                continue
            p = process_info(int(proc.name))
            if not p or p['state'] in ('Z', 'X'):
                continue
            entry = str(ROOT / 'branch_worker.py')
            if entry in p['args']:
                pos = p['args'].index(entry)
                folder = p['args'][pos + 1] if len(p['args']) > pos + 1 else ''
                if folder in folders:
                    task = folders[folder]
                    task.update(status='RUNNING', pid=int(proc.name), start_ticks=p['start_ticks'], entrypoint=entry)
            merge_entry = str(ROOT / 'parents_merger.py')
            if merge_entry in p['args']:
                pos = p['args'].index(merge_entry)
                key = p['args'][pos + 1] if len(p['args']) > pos + 1 else ''
                if key in self.state['parents']:
                    merger = self.state['mergers'].setdefault(key, {'started_epoch': time.time()})
                    merger.update(status='RUNNING', pid=int(proc.name), start_ticks=p['start_ticks'], entrypoint=merge_entry)
        for key, merger in self.state['mergers'].items():
            if merger['status'] == 'STARTING' and not alive(merger):
                merger['status'] = 'UNSTARTED_RECOVERED'
                self.state['parents'][key]['dirty'] = True
        self.save()

    def discover(self):
        rows = self.inputs.rows()
        for key, row in rows.items():
            if not row.get('counts', {}).get('O', 0) or key in self.state['parents']:
                continue
            try:
                a = self.inputs.anchor(row)
                self.state['parents'][key] = {'index': int(key), 'anchor_file': f'anchors/{key}/ANCHOR.json',
                    'last_dispatch': 0, 'dirty': False, 'merge_epoch': 0}
                for path in a['original_open_paths']:
                    task_id = key + '_' + hashlib.sha256(path.encode()).hexdigest()[:20]
                    self.state['tasks'][task_id] = {'task_id': task_id, 'index': int(key),
                        'target_path': path, 'status': 'PENDING', 'folder': 'tasks/' + task_id}
                self.event('PARENT_ANCHORED', index=int(key), original_open=len(a['original_open_paths']),
                           source_certificate_sha256=a['source_certificate_sha256'])
            except Exception:
                self.event('INPUT_SNAPSHOT_ERROR', index=int(key), error=traceback.format_exc())
        self.state['source_unclosed_parents'] = sum(bool(r.get('counts', {}).get('O', 0)) for r in rows.values())
        self.last_discover = time.time()
        self.save()

    def owned(self):
        rows = list(self.state['tasks'].values()) + list(self.state['mergers'].values())
        if self.state.get('alpha_composition'):
            rows.append(self.state['alpha_composition'])
        rows.extend(self.state.get('alpha_composition_extra_processes', []))
        return [r['pid'] for r in rows if r.get('status') in ('RUNNING', 'ALPHA_RETIRING') and alive(r)]

    def start_child(self, entry, args, log_path):
        log_path.parent.mkdir(parents=True, exist_ok=True)
        with log_path.open('ab') as f:
            child = subprocess.Popen([sys.executable, '-B', str(ROOT / entry), *args], cwd=ROOT,
                stdin=subprocess.DEVNULL, stdout=f, stderr=subprocess.STDOUT, start_new_session=True,
                env={**os.environ, 'TMPDIR': str(ROOT / 'tmp')})
        self.children[child.pid] = child
        p = process_info(child.pid)
        if not p:
            raise RuntimeError('New child disappeared before process identity was recorded')
        return {'pid': child.pid, 'start_ticks': p['start_ticks'], 'entrypoint': str(ROOT / entry),
                'started_epoch': time.time(), 'status': 'RUNNING'}

    def next_pending(self):
        pending, active = {}, Counter()
        active_capped = Counter()
        for t in self.state['tasks'].values():
            if t['status'] == 'PENDING':
                pending.setdefault(str(t['index']), []).append(t)
            elif t['status'] == 'RUNNING':
                active[str(t['index'])] += 1
                if len(t['target_path']) >= 100:
                    active_capped[str(t['index'])] += 1
        if not pending:
            return None
        capped = {k: [t for t in ts if len(t['target_path']) >= 100] for k, ts in pending.items()
                  if not active_capped[k] and any(len(t['target_path']) >= 100 for t in ts)}
        if capped:
            # Each formerly depth-capped parent gets an independent deep branch;
            # existing broad searches continue with their unchanged process IDs.
            key = min(capped, key=lambda k: (active[k], self.state['parents'][k]['last_dispatch'], int(k)))
            return min(capped[key], key=lambda t: (len(t['target_path']), t['target_path']))
        key = min(pending, key=lambda k: (active[k], -len(pending[k]), self.state['parents'][k]['last_dispatch'], int(k)))
        # Fixed fair policy: same-parent shortest original path first, deterministic order.
        return min(pending[key], key=lambda t: (len(t['target_path']), t['target_path']))

    def dispatch(self, task):
        if shutil.disk_usage(ROOT).free < self.config['min_disk_free_gib'] * 1024**3:
            return False
        index = task['index']
        parent = self.state['parents'][str(index)]
        anchor = read(ROOT / parent['anchor_file'])
        row, version = self.inputs.latest_for(index, anchor)
        if not dm.counts(dm.at(version['base']['tree'], task['target_path'])).get('O', 0):
            task.update(status='COVERED_BY_PRODUCTION', covered_base_file=version['folder'] + '/base.json',
                covered_migration_file=version['folder'] + '/MIGRATION.json', finished_epoch=time.time())
            parent['dirty'] = True
            self.event('REUSED_COMPLETED_PRODUCTION_BRANCH', task_id=task['task_id'], index=index)
            self.save()
            return False
        folder = ROOT / task['folder']
        folder.mkdir(parents=True, exist_ok=True)
        m = version['migration']
        request = {'schema': 'RHO5_OWNED_OPEN_DEPTH500_TASK_V1', 'task_id': task['task_id'], 'index': index,
            'target_path': task['target_path'], 'parent_file': version['folder'] + '/parent.json',
            'base_file': version['folder'] + '/base.json', 'migration_file': version['folder'] + '/MIGRATION.json',
            'input_sha256': m['base_file_sha256'], 'legacy_input_sha256': row['certificate_sha256'],
            'parent_sha256': m['parent_file_sha256'], 'source_completed_epoch': m['source_completed_epoch'],
            'source_read_epoch': time.time(), 'max_depth': 500, 'milestone_depth': 300,
            'same_pid_after_300': True, 'periodic_restart': False,
            'original_open_anchor_file': parent['anchor_file'], 'original_open_anchor_sha256': dm.file_sha(ROOT / parent['anchor_file'])}
        if (folder / 'TASK.json').exists():
            raise ValueError('Refuse replacing an existing task input')
        atomic_json(folder / 'TASK.json', request)
        # Persist ownership before spawn, allowing restart recovery to adopt the live child.
        task['status'] = 'STARTING'
        self.save()
        task.update(self.start_child('branch_worker.py', [str(folder)], folder / 'WORKER.log'))
        task['input_sha256'] = request['input_sha256']
        task['legacy_input_sha256'] = row['certificate_sha256']
        parent['last_dispatch'] = time.time()
        self.event('BRANCH_STARTED', task_id=task['task_id'], index=index, pid=task['pid'],
            target_depth=len(task['target_path']), legacy_input_sha256=row['certificate_sha256'])
        self.save()
        return True

    def harvest(self):
        for pid, child in list(self.children.items()):
            if child.poll() is not None:
                del self.children[pid]
        for task in self.state['tasks'].values():
            if task['status'] == 'MEMORY_PRESSURE_PAUSED' and not self.memory_pause_record(task):
                folder = ROOT / task['folder']
                # A later user/disk stop supersedes resource auto-resume. Do not
                # let an ineligible paused row block all unrelated new dispatch.
                task['status'] = ('SAVED_UNVERIFIED_STOP' if (folder / 'STOP.json').exists()
                                  else 'MEMORY_PAUSE_RECORD_INVALID')
                self.event('MEMORY_AUTO_RESUME_CANCELLED', task_id=task['task_id'], status=task['status'])
                self.save()
                continue
            if task['status'] not in ('RUNNING', 'STARTING'):
                continue
            if alive(task):
                continue
            folder = ROOT / task['folder']
            try:
                if (folder / 'RESULT.json').exists():
                    result = read(folder / 'RESULT.json')
                    req = read(folder / 'TASK.json')
                    if any(result[k] != req[k] for k in ('task_id', 'index', 'target_path', 'input_sha256', 'parent_sha256')):
                        raise ValueError('Result task binding mismatch')
                    if dm.file_sha(folder / 'final.json') != result['certificate_sha256']:
                        raise ValueError('Result certificate byte mismatch')
                    if result['status'] not in ('CLOSED', 'DEPTH500_OPEN', 'RESOURCE_PAUSED'):
                        raise ValueError('Unknown terminal result status')
                    if result['closed'] != result['verification']['closed'] or result['closed'] != (result['status'] == 'CLOSED'):
                        raise ValueError('Closed receipt mismatch')
                    task.update(status=result['status'], result_sha256=dm.file_sha(folder / 'RESULT.json'),
                        result_certificate_sha256=result['certificate_sha256'], maxdepth=result['maxdepth'])
                    task['closed'] = bool(result['closed'])
                    # Gains are also measured against the concurrent paid production frontier.
                    if result['closed']:
                        try:
                            a = read(ROOT / self.state['parents'][str(task['index'])]['anchor_file'])
                            _, current = self.inputs.latest_for(task['index'], a)
                            task['new_vs_latest_production'] = bool(dm.counts(dm.at(current['base']['tree'], task['target_path'])).get('O', 0))
                            task['comparison_source_certificate_sha256'] = current['migration']['legacy_certificate_file_sha256']
                        except Exception:
                            task['new_vs_latest_production'] = None
                    self.state['parents'][str(task['index'])]['dirty'] = True
                    self.event('BRANCH_EXACT_RESULT', task_id=task['task_id'], index=task['index'],
                               status=task['status'], maxdepth=result['maxdepth'],
                               new_vs_latest_production=task.get('new_vs_latest_production'))
                elif (self.memory_pause_record(task) and (folder / 'final.json').is_file()
                      and not (folder / 'ERROR.json').exists()
                      and ((folder / 'STOPPED.json').exists()
                           or self.memory_pause_record(task).get('forced') is True
                           or task.get('memory_resume_inflight'))):
                    task['status'] = 'MEMORY_PRESSURE_PAUSED'
                    task['memory_paused_epoch'] = time.time()
                    self.event('MEMORY_PRESSURE_CHECKPOINT_RETAINED', task_id=task['task_id'])
                elif (folder / 'STOPPED.json').exists():
                    task['status'] = 'SAVED_UNVERIFIED_STOP'
                else:
                    task['status'] = 'ERROR'
                    if not (folder / 'ERROR.json').exists():
                        atomic_json(folder / 'ERROR.json', {'epoch': time.time(), 'error': 'Worker exited without accepted result; checkpoint preserved',
                            'checkpoint_retained': (folder / 'final.json').exists(), 'closed': False, 'automatic_retry': False})
                    self.event('BRANCH_ERROR', task_id=task['task_id'])
            except Exception:
                task['status'] = 'ERROR'
                atomic_json(folder / 'HARVEST_ERROR.json', {'epoch': time.time(), 'error': traceback.format_exc()})
                self.event('HARVEST_ERROR', task_id=task['task_id'])
            task['finished_epoch'] = time.time()
            self.save()
        for key, merger in self.state['mergers'].items():
            if merger['status'] != 'RUNNING' or alive(merger):
                continue
            parent = self.state['parents'][key]
            path = ROOT / 'parents' / key / 'MERGE_DONE.json'
            error = ROOT / 'parents' / key / 'MERGE_ERROR.json'
            done = read(path) if path.exists() else {}
            coverage = ROOT / 'parents' / key / 'COVERAGE.json'
            if done.get('status') == 'SUCCESS' and done.get('started_epoch', 0) >= merger['started_epoch'] - 1 and coverage.exists() and dm.file_sha(coverage) == done.get('coverage_file_sha256') and not (error.exists() and error.stat().st_mtime >= merger['started_epoch']):
                merger['status'] = 'COMPLETE'
                parent['strict_accepted'] = done.get('strict_accepted', False)
            else:
                merger['status'] = 'ERROR'
                parent['merge_error'] = True
                self.event('MERGER_ERROR', index=int(key))
            parent['merge_epoch'] = time.time()
            self.save()

    def merge_if_ready(self):
        if any(m['status'] == 'RUNNING' and alive(m) for m in self.state['mergers'].values()):
            return False
        # Coalesce structural snapshots; mathematics is performed once, only at whole-parent closure.
        for key, parent in self.state['parents'].items():
            if parent.get('alpha_mode'):
                continue
            if not parent['dirty'] or parent.get('merge_error'):
                continue
            tasks = [t for t in self.state['tasks'].values() if str(t['index']) == key]
            all_closed = all(t['status'] in ('CLOSED', 'COVERED_BY_PRODUCTION', 'COVERED_BY_ALPHA') for t in tasks)
            if not all_closed and time.time() - parent['merge_epoch'] < 120:
                continue
            parent['dirty'] = False
            self.state['mergers'][key] = {'status': 'STARTING', 'index': int(key),
                'entrypoint': str(ROOT / 'parents_merger.py'), 'started_epoch': time.time()}
            self.save()
            folder = ROOT / 'parents' / key
            folder.mkdir(parents=True, exist_ok=True)
            args = [key] + (['full_check'] if all_closed else [])
            self.state['mergers'][key] = self.start_child('parents_merger.py', args, folder / 'MERGER.log')
            self.event('PARENT_MERGE_STARTED', index=int(key), full_check=all_closed)
            self.save()
            return True
        return False

    def status(self, phase):
        now = time.time()
        tasks = self.state['tasks'].values()
        counter = Counter(t['status'] for t in tasks)
        per_parent = []
        for key, parent in self.state['parents'].items():
            subset = [t for t in tasks if str(t['index']) == key]
            per_parent.append({'index': int(key), 'original_open_branches': len(subset),
                               'statuses': dict(Counter(t['status'] for t in subset))})
        progresses = []
        for t in tasks:
            if t['status'] != 'RUNNING':
                continue
            path = ROOT / t['folder'] / 'PROGRESS.json'
            p = read(path) if path.exists() else {}
            progresses.append({'task_id': t['task_id'], 'index': t['index'], 'pid': t.get('pid'),
                              'target_depth': len(t['target_path']), **p})
        strict = []
        for key in self.state['parents']:
            p = ROOT / 'parents' / key / 'STRICT_DEEP500_RESULT.json'
            if p.exists():
                strict.append(int(key))
        status = {'schema': 'RHO5_ALL_OPEN_BRANCH_DEPTH500_STATUS_V1', 'phase': phase, 'epoch': now,
            'daemon_pid': os.getpid(), 'started_epoch': self.state['started_epoch'],
            'scope': 'ALL_CURRENTLY_UNCLOSED_X_SYNCHRONIZED_PARENTS',
            'parents': len(self.state['parents']), 'source_unclosed_parents': self.state.get('source_unclosed_parents'),
            'original_open_branches': len(self.state['tasks']), 'statuses': dict(counter),
            'new_verified_original_branches_closed': counter['CLOSED'] + counter['COVERED_BY_ALPHA'],
            'new_verified_alpha_original_branches_closed': counter['COVERED_BY_ALPHA'],
            'alpha_searches_retiring': counter['ALPHA_RETIRING'],
            'strict_alpha_composite_parents': [int(k) for k,p in self.state['parents'].items() if p.get('alpha_strict_accepted')],
            'closed_still_open_in_production_at_acceptance': sum(t.get('new_vs_latest_production') is True for t in tasks),
            'already_covered_by_production': counter['COVERED_BY_PRODUCTION'],
            'strict_deep500_parents': strict, 'legacy_root_credit_claimed': False,
            'active_search_workers': counter['RUNNING'], 'active_mergers': sum(m['status'] == 'RUNNING' for m in self.state['mergers'].values()),
            'capacity': self.last_capacity, 'per_parent': per_parent, 'active_progress': progresses,
            'max_depth': 500, 'milestone_depth': 300, 'milestone_restarts': False,
            'search_time_limit_seconds': None, 'model_wakeups': False}
        atomic_json(ROOT / 'STATUS.json', status)
        self.last_status = now

    def run(self):
        def stop(_sig, _frame):
            self.stop_signal = True
        signal.signal(signal.SIGTERM, stop)
        signal.signal(signal.SIGINT, stop)
        while True:
            self.harvest()
            try:
                if self.alpha_bridge is not None:
                    self.alpha_bridge.update()
            except Exception:
                atomic_json(ROOT / "alpha_v1/BRIDGE_ERROR.json", {"epoch": time.time(), "error": traceback.format_exc(), "old_searches_preserved": True})
                self.event("ALPHA_BRIDGE_ERROR", error=traceback.format_exc())
                if self.alpha_bridge is not None:
                    self.alpha_bridge.enabled = False
            stopping = self.stop_signal or (ROOT / 'STOP.json').exists()
            if stopping:
                if not (ROOT / 'STOP.json').exists():
                    atomic_json(ROOT / 'STOP.json', {'epoch': time.time(), 'reason': 'Supervisor stop signal'})
                stopping_mergers = list(self.state['mergers'].values())
                if self.state.get('alpha_composition'):
                    stopping_mergers.append(self.state['alpha_composition'])
                stopping_mergers.extend(self.state.get('alpha_composition_extra_processes', []))
                for merger in stopping_mergers:
                    if merger['status'] == 'RUNNING' and alive(merger) and not merger.get('stop_sent'):
                        os.kill(merger['pid'], signal.SIGTERM)
                        merger['stop_sent'] = True
                        self.save()
                self.status('STOPPING' if self.owned() else 'STOPPED')
                if not self.owned():
                    self.event('STOPPED_CHECKPOINTS_PRESERVED')
                    return
                time.sleep(2)
                continue
            if time.time() - self.last_discover >= 60:
                self.discover()
            self.last_capacity = capacity_sample(ROOT, self.owned(), self.config)
            free_disk = shutil.disk_usage(ROOT).free
            self.last_capacity['disk_free_bytes'] = free_disk
            self.last_capacity['disk_reserve_bytes'] = self.config['min_disk_free_gib'] * 1024**3
            if free_disk < self.last_capacity['disk_reserve_bytes']:
                self.last_capacity['dispatch_slots'] = 0
                # Stop only our searches at their already durable checkpoints.
                # The 12 GiB reserve covers in-flight atomic writes as they exit.
                for t in self.state['tasks'].values():
                    if t['status'] == 'RUNNING' and alive(t):
                        p = ROOT / t['folder'] / 'STOP.json'
                        if not p.exists():
                            atomic_json(p, {'reason': 'DISK_RESOURCE_PAUSE', 'epoch': time.time(),
                                'disk_free_bytes': free_disk, 'checkpoint_preserved': True})
                atomic_json(ROOT / 'RESOURCE_GUARD.json', {'status': 'DISK_RESOURCE_PAUSE', 'epoch': time.time(),
                    'disk_free_bytes': free_disk, 'automatic_retry': False})
            guard = self.memory_guard_status()
            self.last_capacity['memory_guard'] = guard
            if not guard['healthy']:
                self.last_capacity['dispatch_slots'] = 0
                self.last_capacity['memory_guard_blocks_admission'] = True
            # Bounded startup bursts permit actual RSS to appear before refill.
            slots = min(self.last_capacity['dispatch_slots'], int(self.config.get('dispatch_batch_size', 2)))
            stable_since = guard.get('stable_available_since')
            paused = [t for t in self.state['tasks'].values() if t['status'] == 'MEMORY_PRESSURE_PAUSED']
            if slots > 0 and paused:
                # Pause recovery requires stable spare memory and a per-task
                # cooldown; pressure cannot create a rapid restart loop.
                if (stable_since and time.time() - stable_since >= 60
                        and time.time() - self.state.get('last_memory_resume_epoch', 0) >= 10):
                    for task in sorted(paused, key=lambda t: t.get('memory_paused_epoch', 0)):
                        cooldown = min(3600, 60 * 2 ** min(task.get('memory_resume_count', 0), 6))
                        if time.time() - task.get('memory_paused_epoch', 0) < cooldown:
                            continue
                        try:
                            if self.resume_memory_task(task):
                                slots -= 1
                                self.state['last_memory_resume_epoch'] = time.time()
                                self.save()
                                break
                        except Exception:
                            task.update(status='MEMORY_RESUME_ERROR', error=traceback.format_exc())
                            self.event('MEMORY_RESUME_ERROR', task_id=task['task_id'], error=task['error'])
                            self.save()
                # Existing saved work has priority over new work after pressure.
                slots = 0

            if slots > 0 and self.merge_if_ready():
                slots -= 1
            attempts = 0
            while slots > 0:
                if (ROOT / 'STOP.json').exists() or not self.memory_guard_status()['healthy']:
                    break
                task = self.next_pending()
                if task is None:
                    break
                try:
                    if self.dispatch(task):
                        slots -= 1
                except Exception:
                    task['status'] = 'INPUT_ERROR'
                    task['error'] = traceback.format_exc()
                    self.event('DISPATCH_ERROR', task_id=task['task_id'], error=task['error'])
                    self.save()
                attempts += 1
                if attempts >= 64 or time.time() - self.last_status > 15:
                    self.status('RUNNING')
                    if attempts >= 64:
                        break
            counter = Counter(t['status'] for t in self.state['tasks'].values())
            phase = 'RUNNING' if self.owned() or counter['PENDING'] or counter['MEMORY_PRESSURE_PAUSED'] else 'WAITING_FOR_NEW_SOURCE_OR_USER'
            self.status(phase)
            if self.state['tasks'] and all(t['status'] in ('CLOSED', 'COVERED_BY_PRODUCTION', 'COVERED_BY_ALPHA') for t in self.state['tasks'].values()) and not self.owned() and all(not p['dirty'] and not p.get('merge_error') and p.get('strict_accepted') for p in self.state['parents'].values()):
                self.status('COMPLETE')
                self.event('ALL_ORIGINAL_OPEN_BRANCHES_CLOSED')
                return
            time.sleep(float(self.config.get('coordinator_poll_seconds', 2)))


def main():
    os.nice(max(0, 10 - os.getpriority(os.PRIO_PROCESS, 0)))
    lock = (ROOT / 'DAEMON.lock').open('a+')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    try:
        Coordinator().run()
    except BaseException:
        error = {'epoch': time.time(), 'error': traceback.format_exc(), 'checkpoints_retained': True,
                 'automatic_retry': False, 'pid': os.getpid()}
        atomic_json(ROOT / 'DAEMON_ERROR.json', error)
        # Only our children observe this file; existing production is untouched.
        atomic_json(ROOT / 'STOP.json', {'epoch': time.time(), 'reason': 'Coordinator error; save local worker checkpoints'})
        raise


if __name__ == '__main__':
    main()
