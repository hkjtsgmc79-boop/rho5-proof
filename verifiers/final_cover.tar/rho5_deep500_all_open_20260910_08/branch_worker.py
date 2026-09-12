"""One continuous exact-discovery branch, with durable atomic checkpoints.

Search is untrusted. Only deep_math.verify_branch can grant a closed branch.
No wall-clock or per-round node budget restarts this worker.
"""
from pathlib import Path
import copy
import hashlib
import json
import os
import resource
import signal
import sys
import time
import traceback
import threading

sys.setrecursionlimit(10000)
sys.dont_write_bytecode = True
for _key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[_key] = '1'
ROOT = Path(__file__).resolve().parent
MAX_DEPTH = 500
MILESTONE_DEPTH = 300
MAX_TARGET_NODES = 200000
MAX_CHECKPOINT_BYTES = 256 * 1024**2
# The existing admission allowance is 4 GiB for the entire process group.
MEMORY_LIMIT = 3 * 1024**3
SOLVER_MEMORY_LIMIT = 1 * 1024**3
PROGRESS_INTERVAL = 15.0

from fast_checkpoint import atomic_json
import deep_math


class UserStop(Exception):
    pass


class ResourcePause(Exception):
    pass


def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text())


def owned_path(value):
    p = (ROOT / value).resolve()
    if not p.is_relative_to(ROOT):
        raise ValueError('Task file is outside the isolated run directory')
    return p


def has_open(node):
    term = node['terminal']
    if term['kind'] == 'O':
        return True
    return term['kind'] == 'S' and (has_open(term['left']) or has_open(term['right']))


def path_is_owned(target, path):
    return target.startswith(path) or path.startswith(target)


def _split_axis(rows, boxes, profile, db, fs, Q):
    # Exact copy of the frozen V44 proposal policy; only dependencies are arguments.
    import numpy as np
    from scipy.optimize import linprog
    n = len(boxes)
    center = np.array([float((b.lo + b.hi) / 2) for b in boxes])
    half = np.array([float((b.hi - b.lo) / 2) for b in boxes])
    matrix = np.zeros((len(rows), n))
    rhs = np.zeros(len(rows))
    for i, (a, b) in enumerate(rows):
        rhs[i] = float(b)
        for j, c in a.items():
            matrix[i, j] = float(c)
    b = rhs - matrix @ center
    a = matrix * half
    scale = np.maximum(1e-9, np.maximum(abs(b), np.max(abs(a), axis=1)))
    objective = np.zeros(n)
    objective[23] = -half[23]
    result = linprog(objective, A_ub=a / scale[:, None], b_ub=b / scale,
                     bounds=[(-1, 1)] * n, method='highs', options={'time_limit': 1.0})
    score = half[:24] * 0.001
    polys = fs.BASE_POLYS + (db.WINDOW_ROWS if profile in ('PIVOT', 'PIVOT_CYCLE') else [])
    pairs = sorted({m for _, p in polys for m in p if len(m) == 2})
    if n != 24 + len(pairs):
        raise ValueError('Unrecognized discovery column layout')
    if result.success:
        x = center + half * result.x
        for h, (i, j) in enumerate(pairs):
            error = abs(x[24 + h] - x[i] * x[j])
            if i == j:
                score[i] += error
            else:
                den = half[i] + half[j] + 1e-100
                score[i] += error * half[i] / den
                score[j] += error * half[j] / den
    axis = int(np.argmax(score))
    if boxes[axis].lo >= boxes[axis].hi:
        raise ValueError('No nondegenerate split available')
    return axis


class BranchWorker:
    def __init__(self, folder):
        self.folder = owned_path(str(folder))
        self.task = read_json(self.folder / 'TASK.json')
        self.target = self.task['target_path']
        if not isinstance(self.target, str) or any(c not in '01' for c in self.target):
            raise ValueError('Invalid target path')
        self.parent_path = owned_path(self.task['parent_file'])
        self.base_path = owned_path(self.task['base_file'])
        if file_sha(self.base_path) != self.task['input_sha256']:
            raise ValueError('Base certificate byte identity mismatch')
        if file_sha(self.parent_path) != self.task['parent_sha256']:
            raise ValueError('Parent byte identity mismatch')
        self.parent, self.base = read_json(self.parent_path), read_json(self.base_path)
        if self.parent['index'] != self.task['index']:
            raise ValueError('Parent index mismatch')
        if not has_open(deep_math.at(self.base['tree'], self.target)):
            raise ValueError('Assigned original target already has no OPEN descendants')
        self.bp = deep_math.load_protocol(ROOT)
        self.final_path = self.folder / 'final.json'
        self.resumed = self.final_path.exists()
        if self.resumed:
            self.cert = read_json(self.final_path)
            deep_math.validate_branch_extension(self.base, self.cert, self.target)
        else:
            self.cert = {k: v for k, v in self.base.items() if k != 'tree'}
            self.cert['tree'] = deep_math.project(self.base['tree'], self.target)
            deep_math.validate_branch_extension(self.base, self.cert, self.target)
        self.profile = self.cert['profile']
        self.bp.db.validate_profile(self.profile)
        self.started_wall, self.started_cpu = time.monotonic(), time.process_time()
        previous = read_json(self.folder / 'PROGRESS.json') if self.resumed and (self.folder / 'PROGRESS.json').exists() else {}
        self.prior_cpu = previous.get('cpu_seconds', 0.0)
        self.prior_solver_cpu = previous.get('lp_solver_cpu_seconds', 0.0)
        self.prior_lp_timeouts = previous.get('lp_timeout_count', 0)
        self.prior_lp_failures = previous.get('lp_failure_count', 0)
        self.prior_lp_calls = previous.get('lp_call_count', 0)
        self.lp_guard = None
        self.prior_wall = previous.get('wall_seconds', 0.0)
        self.visits = previous.get('visits', 0)
        self.open_visits = previous.get('open_visits', 0)
        self.new_splits = previous.get('new_splits', 0)
        self.save_cpu = previous.get('save_cpu_seconds', 0.0)
        self.save_wall = previous.get('save_wall_seconds', 0.0)
        self.save_count = previous.get('save_calls', 0)
        self.last_progress = 0.0
        self.last_save_bytes = self.final_path.stat().st_size if self.resumed else 0
        self.target_counts = deep_math.counts(deep_math.at(self.cert['tree'], self.target))
        self.maxdepth = len(self.target) + self.target_counts.get('maxdepth', 0)
        self.current_path = self.target
        self.stop_signal = None
        self.last_good_saved = self.resumed
        self.reason = None
        self.phase = 'SEARCHING'
        self.heartbeat_stop = threading.Event()

    def stop_requested(self):
        return self.stop_signal is not None or (ROOT / 'STOP.json').exists() or (self.folder / 'STOP.json').exists()

    def progress(self, phase=None, force=False):
        if phase is not None:
            self.phase = phase
        phase = self.phase
        now = time.monotonic()
        if not force and now - self.last_progress < PROGRESS_INTERVAL:
            return
        self.last_progress = now
        guard = self.lp_guard
        solver_cpu = guard.total_solver_cpu_seconds if guard is not None else 0.0
        value = {'task_id': self.task['task_id'], 'index': self.task['index'],
                 'target_path': self.target, 'phase': phase, 'pid': os.getpid(),
                 'epoch': time.time(), 'resumed': self.resumed, 'current_path': self.current_path,
                 'cpu_seconds': self.prior_cpu + time.process_time() - self.started_cpu + solver_cpu,
                 'lp_solver_cpu_seconds': self.prior_solver_cpu + solver_cpu,
                 'lp_timeout_count': self.prior_lp_timeouts + (guard.timeout_count if guard is not None else 0),
                 'lp_failure_count': self.prior_lp_failures + (guard.failure_count if guard is not None else 0),
                 'lp_call_count': self.prior_lp_calls + (guard.sequence if guard is not None else 0),
                 'parent_memory_limit_bytes': MEMORY_LIMIT, 'solver_memory_limit_bytes': SOLVER_MEMORY_LIMIT,
                 'wall_seconds': self.prior_wall + now - self.started_wall,
                 'visits': self.visits, 'open_visits': self.open_visits,
                 'new_splits': self.new_splits, 'maxdepth': self.maxdepth,
                 'target_counts': dict(self.target_counts), 'save_cpu_seconds': self.save_cpu,
                 'save_wall_seconds': self.save_wall, 'save_calls': self.save_count,
                 'checkpoint_bytes': self.last_save_bytes,
                 'max_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                 'search_depth_limit': MAX_DEPTH, 'model_wakeups': False}
        atomic_json(self.folder / 'PROGRESS.json', value)

    def safe_point(self):
        self.progress()
        if self.stop_requested():
            raise UserStop('Explicit user stop or termination signal')
        if self.target_counts.get('nodes', 0) > MAX_TARGET_NODES:
            raise ResourcePause('TARGET_NODE_LIMIT: existing target exceeds 200000 nodes')
        # Parent RLIMIT_AS is 3 GiB; the solver child has its own reserved 1 GiB.
        # Leave space for one checkpoint serialization within the parent limit.
        stat = Path('/proc/self/status')
        if stat.exists():
            for line in stat.read_text().splitlines():
                if line.startswith('VmSize:') and int(line.split()[1]) * 1024 >= MEMORY_LIMIT - 384 * 1024**2:
                    raise ResourcePause('MEMORY_RESERVE: parent virtual address space near 3 GiB limit (1 GiB solver reserve)')

    def save(self):
        sc, sw = time.process_time(), time.monotonic()
        try:
            atomic_json(self.final_path, self.cert, max_bytes=MAX_CHECKPOINT_BYTES)
        except ValueError as exc:
            if 'CHECKPOINT_TOO_LARGE' in str(exc):
                raise ResourcePause('CHECKPOINT_TOO_LARGE: 256 MiB checkpoint limit') from exc
            raise
        finally:
            self.save_cpu += time.process_time() - sc
            self.save_wall += time.monotonic() - sw
        self.save_count += 1
        self.last_good_saved = True
        self.last_save_bytes = self.final_path.stat().st_size

    def milestone(self, path):
        record = self.folder / 'DEPTH300.json'
        if len(path) != MILESTONE_DEPTH or record.exists():
            return
        snapshot = self.folder / 'depth300_certificate.json'
        # Atomic replacement of final.json gives an immutable hardlinked snapshot.
        if not snapshot.exists():
            os.link(self.final_path, snapshot)
        atomic_json(record, {'epoch': time.time(), 'pid': os.getpid(),
                            'task_id': self.task['task_id'], 'index': self.task['index'],
                            'target_path': self.target, 'reached_path': path,
                            'milestone_depth': MILESTONE_DEPTH,
                            'meaning': ('FIRST_REACHED_DEPTH_300_NOT_EXHAUSTIVE_DEPTH_300_RUN'
                                        if self.maxdepth == MILESTONE_DEPTH else
                                        'FIRST_OBSERVED_DEPTH_300_ON_RESUMED_DEEPER_CHECKPOINT'),
                            'same_process_continues': True, 'search_restarted': False,
                            'checkpoint_sha256': file_sha(snapshot),
                            'checkpoint_file': str(snapshot.relative_to(ROOT)),
                            'target_counts': deep_math.counts(deep_math.at(self.cert['tree'], self.target)),
                            'maxdepth': self.maxdepth,
                            'cpu_seconds': self.prior_cpu + time.process_time() - self.started_cpu
                                           + (self.lp_guard.total_solver_cpu_seconds if self.lp_guard is not None else 0.0),
                            'save_cpu_seconds': self.save_cpu,
                            'mathematical_acceptance': 'PENDING_FINAL_BRANCH_CHECK'})
        self.progress(force=True)

    def terminal(self, node, terminal):
        assert node['terminal']['kind'] == 'O'
        node['terminal'] = terminal
        self.target_counts['O'] = self.target_counts.get('O', 0) - 1
        kind = terminal['kind']
        self.target_counts[kind] = self.target_counts.get(kind, 0) + 1
        self.save()

    def visit(self, inbox, node, depth, path=''):
        # Exterior siblings are retained as O in the projection and never searched.
        if not path_is_owned(self.target, path):
            return
        self.current_path = path
        self.safe_point()
        if not has_open(node):
            return
        self.visits += 1
        self.milestone(path)
        db, fs, Q = self.bp.db, self.bp.fs, self.bp.Q
        o = db.common_contract(inbox, profile=self.profile)
        for wave in node['waves']:
            o = db.apply_wave(o, wave, profile=self.profile, cross_check=False)
        term = node['terminal']
        if term['kind'] == 'S':
            ax = term['axis']
            b = o['aux_image']
            lo, hi = map(Q, b[ax])
            mid = (lo + hi) / 2
            l, r = copy.deepcopy(b), copy.deepcopy(b)
            l[ax][1], r[ax][0] = str(mid), str(mid)
            self.visit({'status': 'BOUNDED', 'aux_image': l}, term['left'], depth + 1, path + '0')
            self.visit({'status': 'BOUNDED', 'aux_image': r}, term['right'], depth + 1, path + '1')
            return
        if term['kind'] != 'O':
            return
        if not path.startswith(self.target):
            raise ValueError('Target ancestor is not a split')
        self.open_visits += 1
        from discovery import bound_proposals
        from proposal import propose_rows
        for turn in range(2):  # Frozen policy: waves_per_node = 1.
            self.safe_point()
            if o['status'] == 'EMPTY':
                self.terminal(node, {'kind': 'I'})
                return
            if fs.safe_port(o['aux_image']) is not None:
                self.terminal(node, {'kind': 'A'})
                return
            rows, boxes = db.rows_and_bounds(o['aux_image'], profile=self.profile)
            t = propose_rows(rows, boxes)
            if t:
                self.terminal(node, t)
                return
            if turn == 1 or len(node['waves']) >= 128:
                break
            self.safe_point()
            wave = bound_proposals(rows, boxes, float('inf'), limit=16)
            if not wave:
                break
            # Apply fully and check exactly before the recorded tree is changed.
            next_image = db.apply_wave(o, wave, profile=self.profile, cross_check=True)
            node['waves'].append(wave)
            o = next_image
            self.target_counts['new_waves'] = self.target_counts.get('new_waves', 0) + 1
            self.target_counts['new_bounds'] = self.target_counts.get('new_bounds', 0) + len(wave)
            self.save()
        self.safe_point()
        if depth >= MAX_DEPTH:
            return
        if self.target_counts['nodes'] + 2 > MAX_TARGET_NODES:
            raise ResourcePause('TARGET_NODE_LIMIT: 200000 nodes in original target subtree')
        ax = _split_axis(rows, boxes, self.profile, db, fs, Q)
        b = o['aux_image']
        lo, hi = map(Q, b[ax])
        mid = (lo + hi) / 2
        if not lo < mid < hi:
            raise ValueError('Degenerate proposed split')
        l, r = copy.deepcopy(b), copy.deepcopy(b)
        l[ax][1], r[ax][0] = str(mid), str(mid)
        node['terminal'] = {'kind': 'S', 'axis': ax,
                            'left': {'waves': [], 'terminal': {'kind': 'O'}},
                            'right': {'waves': [], 'terminal': {'kind': 'O'}}}
        self.new_splits += 1
        self.target_counts['nodes'] += 2
        self.target_counts['S'] = self.target_counts.get('S', 0) + 1
        self.target_counts['O'] = self.target_counts.get('O', 0) + 1
        self.target_counts['maxdepth'] = max(self.target_counts.get('maxdepth', 0), depth + 1 - len(self.target))
        self.maxdepth = max(self.maxdepth, depth + 1)
        self.save()
        self.visit({'status': 'BOUNDED', 'aux_image': l}, node['terminal']['left'], depth + 1, path + '0')
        self.visit({'status': 'BOUNDED', 'aux_image': r}, node['terminal']['right'], depth + 1, path + '1')

    def verify_and_finish(self, status):
        # In a size/memory pause the last saved certificate is the durable result.
        self.cert = None
        import gc
        gc.collect()
        self.cert = read_json(self.final_path)
        self.target_counts = deep_math.counts(deep_math.at(self.cert['tree'], self.target))
        self.maxdepth = len(self.target) + self.target_counts.get('maxdepth', 0)
        self.progress('VERIFYING', force=True)
        if self.stop_requested():
            raise UserStop('Stop before final exact verification')
        verification = deep_math.verify_branch(ROOT, self.parent, self.base, self.cert, self.target)
        closed = verification['closed']
        result = {'status': 'CLOSED' if closed else status,
                  'closed': closed, 'task_id': self.task['task_id'], 'index': self.task['index'],
                  'target_path': self.target, 'input_sha256': self.task['input_sha256'],
                  'parent_sha256': self.task['parent_sha256'],
                  'certificate_sha256': file_sha(self.final_path),
                  'verification': verification, 'target_counts': self.target_counts,
                  'maxdepth': self.maxdepth, 'reason': self.reason, 'pid': os.getpid(),
                  'epoch': time.time(), 'milestone300_recorded': (self.folder / 'DEPTH300.json').exists(),
                  'projection_only': True, 'whole_parent_credit': False}
        atomic_json(self.folder / 'RESULT.json', result)
        self.progress(result['status'], force=True)
        print(json.dumps({k: result[k] for k in ('status', 'closed', 'task_id', 'index', 'maxdepth')}), flush=True)

    def run(self):
        def signal_handler(sig, _frame):
            self.stop_signal = sig
            if self.phase == 'VERIFYING':
                raise UserStop('User stop during final verification; checkpoint retained')
        signal.signal(signal.SIGTERM, signal_handler)
        signal.signal(signal.SIGINT, signal_handler)
        atomic_json(self.folder / 'START.json', {'epoch': time.time(), 'pid': os.getpid(),
                                              'task_id': self.task['task_id'], 'resumed': self.resumed,
                                              'input_sha256': self.task['input_sha256'],
                                              'target_path': self.target, 'max_depth': MAX_DEPTH,
                                              'periodic_restart': False})
        def heartbeat():
            while not self.heartbeat_stop.wait(PROGRESS_INTERVAL):
                try:
                    self.progress(force=True)
                    if self.stop_requested() and self.phase == 'VERIFYING':
                        os.kill(os.getpid(), signal.SIGTERM)
                except Exception:
                    # Progress telemetry must never corrupt or terminate search.
                    pass
        thread = threading.Thread(target=heartbeat, daemon=True, name='branch-progress')
        thread.start()
        try:
            try:
                if not self.resumed:
                    self.save()
                self.safe_point()
                out, _old = self.bp.prefix_image(self.parent, False)
                self.visit(out, self.cert['tree'], 0)
                final_status = 'DEPTH500_OPEN'
            except ResourcePause as exc:
                self.reason = str(exc)
                final_status = 'RESOURCE_PAUSED'
            except MemoryError:
                self.reason = 'MEMORY_LIMIT: 3 GiB parent address-space limit; 1 GiB reserved for isolated solver'
                # Release an unsaved extension before loading the atomic checkpoint.
                self.cert = None
                import gc
                gc.collect()
                final_status = 'RESOURCE_PAUSED'
            self.verify_and_finish(final_status)
        except UserStop as exc:
            self.reason = str(exc)
            atomic_json(self.folder / 'STOPPED.json', {'status': 'SAVED_UNVERIFIED_STOP',
                        'epoch': time.time(), 'pid': os.getpid(), 'task_id': self.task['task_id'],
                        'reason': self.reason, 'checkpoint_retained': self.final_path.exists(),
                        'certificate_sha256': file_sha(self.final_path) if self.final_path.exists() else None,
                        'closed': False, 'mathematical_acceptance': 'NOT_CLAIMED'})
            self.progress('SAVED_UNVERIFIED_STOP', force=True)
        finally:
            self.heartbeat_stop.set()


def configure_process():
    os.nice(max(0, 10 - os.getpriority(os.PRIO_PROCESS, 0)))
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY_LIMIT, MEMORY_LIMIT))
    os.environ['TMPDIR'] = str(ROOT / 'tmp')
    from scipy import optimize
    import functools
    original = optimize.linprog
    @functools.wraps(original)
    def single_thread(*args, **kw):
        method = kw.get('method', 'highs')
        if isinstance(method, str) and method.startswith('highs'):
            options = dict(kw.get('options') or {})
            options['threads'] = 1
            kw['options'] = options
        return original(*args, **kw)
    optimize.linprog = single_thread


def main():
    if len(sys.argv) != 2:
        raise SystemExit('Usage: branch_worker.py <job_folder>')
    folder = owned_path(sys.argv[1])
    if (folder / 'RESULT.json').exists():
        print(json.dumps({'status': 'EXISTING_RESULT_NO_NEW_BUDGET', 'folder': str(folder)}), flush=True)
        return
    try:
        configure_process()
        worker = BranchWorker(folder)
        # Install after the legacy single-thread wrapper and all input loading.
        # Frozen dynamic imports and an already loaded proposal.linprog both use
        # the guard; only an individual solver child can be restarted on timeout.
        from lp_guard import install
        guard = install(folder / 'lp_guard', hard_timeout_seconds=10.0,
                        helper_memory_bytes=SOLVER_MEMORY_LIMIT,
                        context_provider=lambda: {'task_id': worker.task['task_id'],
                                                  'path': worker.current_path,
                                                  'phase': worker.phase})
        worker.lp_guard = guard
        try:
            worker.run()
        finally:
            guard.close()
    except BaseException:
        atomic_json(folder / 'ERROR.json', {'epoch': time.time(), 'pid': os.getpid(),
                    'error': traceback.format_exc(), 'checkpoint_retained': (folder / 'final.json').exists(),
                    'closed': False, 'automatic_retry': False})
        raise


if __name__ == '__main__':
    main()
