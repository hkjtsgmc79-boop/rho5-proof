"""Independent immutable root acceptance; never edits the running search state.

Uses the byte-preserved old R54/V44 apply + full Fraction replay exactly once.
Depth-500 parents are admitted here only if their actual final depth <= 128;
the tree/profile are unchanged and the envelope is explicitly rebound to V44.
"""
from pathlib import Path
from collections import Counter
import argparse
import gc
import hashlib
import json
import os
import resource
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import traceback

sys.dont_write_bytecode = True
sys.setrecursionlimit(10000)
ROOT = Path(__file__).resolve().parent
GIB = 1024 ** 3
OLD_RULE = 'V44_POST_U41_FULL_IMAGE_BISECTION_V1'
DEEP_RULE = 'V44_POST_U41_FULL_IMAGE_BISECTION_DEPTH500_V1'
KEYS = ('index', 'path', 'box', 'box_sha256', 'partial_certificate', 'sample')
DEFAULT_PROD = '/root/microscope_ws/rho5_cqg_continuous_20260910/run_01'
DEFAULT_DEEP = '/root/microscope_ws/rho5_deep500_all_open_20260910_08'


def encoded(x):
    return json.dumps(x, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()


def digest(x):
    return hashlib.sha256(encoded(x)).hexdigest()


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 ** 2), b''):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def atomic(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=path.name + '.', suffix='.tmp')
    try:
        with os.fdopen(fd, 'wb') as f:
            f.write(encoded(value) + b'\n')
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


def child(root, name):
    root = Path(root).resolve()
    p = (root / name).resolve()
    if not p.is_relative_to(root):
        raise ValueError('Input path escapes its declared source root')
    return p


def counts(tree):
    c = Counter()
    stack = [(tree, 0)]
    while stack:
        n, depth = stack.pop()
        if depth > 128:
            raise ValueError('Actual tree exceeds original frozen V44 limit')
        if set(n) != {'waves', 'terminal'}:
            raise ValueError('Malformed local proof node')
        c['nodes'] += 1
        c['maxdepth'] = max(c['maxdepth'], depth)
        c['new_waves'] += len(n['waves'])
        c['new_bounds'] += sum(map(len, n['waves']))
        t = n['terminal']
        c[t['kind']] += 1
        if t['kind'] == 'S':
            if set(t) != {'kind', 'axis', 'left', 'right'}:
                raise ValueError('Incomplete local split')
            stack.extend([(t['right'], depth + 1), (t['left'], depth + 1)])
    if c['nodes'] != 2 * c['S'] + 1:
        raise ValueError('Incomplete local tree')
    return dict(c)


def equal_counts(a, b):
    return all(a.get(k, 0) == b.get(k, 0) for k in set(a) | set(b))


def memory_available():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):
            return int(line.split()[1]) * 1024
    raise RuntimeError('Cannot read available memory')


def configure(config):
    for name in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS',
                 'NUMEXPR_NUM_THREADS', 'BLIS_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS'):
        os.environ[name] = '1'
    os.environ['OMP_THREAD_LIMIT'] = '1'
    os.environ['HIGHS_THREADS'] = '1'
    os.environ['PYTHONDONTWRITEBYTECODE'] = '1'
    os.environ['TMPDIR'] = str(ROOT / 'tmp')
    (ROOT / 'tmp').mkdir(exist_ok=True)
    if os.getpriority(os.PRIO_PROCESS, 0) < 10:
        os.setpriority(os.PRIO_PROCESS, 0, 10)
    requested = min(8, int(config['workers']))
    available = memory_available()
    room = available - config['system_reserve_gib'] * GIB - config['main_memory_reserve_gib'] * GIB
    workers = min(requested, max(0, int(room // (config['worker_memory_reserve_gib'] * GIB))))
    if workers < 1:
        raise RuntimeError('Insufficient memory for independent root replay; no searches changed')
    affinity = sorted(os.sched_getaffinity(0))
    workers = min(workers, len(affinity))
    # The coordinator, pool, and strict child workers collectively cannot use
    # more than these eight logical cores even during parallel submission.
    os.sched_setaffinity(0, affinity[:workers])
    limit = int(config['process_memory_gib'] * GIB)
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    if hard != resource.RLIM_INFINITY:
        limit = min(limit, hard)
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    return {'workers': workers, 'cpu_affinity': affinity[:workers],
            'initial_mem_available_bytes': available, 'process_address_space_limit_bytes': limit,
            'total_task_pss_limit_bytes': int(config['total_task_pss_gib'] * GIB),
            'memory_reservation_model': '24 GiB main root allowance plus 1 GiB per verifier worker',
            'nice': os.getpriority(os.PRIO_PROCESS, 0), 'library_threads': 1}


def task_memory(stage_pid=None):
    rows = {}
    page = os.sysconf('SC_PAGE_SIZE')
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():
            continue
        try:
            text = (p / 'stat').read_text()
            s = text[text.rindex(')') + 2:].split()
            rows[int(p.name)] = (int(s[1]), max(0, int(s[21])) * page)
        except (OSError, ValueError, IndexError):
            continue
    owned = {os.getpid()}
    if stage_pid is not None:
        owned.add(stage_pid)
    changed = True
    while changed:
        changed = False
        for pid, (parent, _rss) in rows.items():
            if parent in owned and pid not in owned:
                owned.add(pid)
                changed = True
    total_pss = 0
    pss_available = True
    for pid in owned:
        try:
            rollup = Path('/proc') / str(pid) / 'smaps_rollup'
            values = [line for line in rollup.read_text().splitlines() if line.startswith('Pss:')]
            if len(values) != 1:
                raise ValueError('No PSS entry')
            total_pss += int(values[0].split()[1]) * 1024
        except FileNotFoundError:
            # A just-exited process no longer consumes memory.
            if (Path('/proc') / str(pid)).exists():
                pss_available = False
        except (PermissionError, ValueError, OSError):
            pss_available = False
    # Never sum RSS as a hard limit: shared pages would be multiplied. If PSS
    # is unavailable, per-process address-space and MemAvailable remain guards.
    return (total_pss if pss_available else None), sorted(owned)


def snapshot(config):
    """All inputs are immutable local copies; completed source files only."""
    prod, deep = Path(config['source_root']).resolve(), Path(config['deep_root']).resolve()
    if (ROOT / 'SNAPSHOT.json').exists():
        raise ValueError('Refuse taking another snapshot in this acceptance task')
    state_bytes = (prod / 'STATE.json').read_bytes()
    state = json.loads(state_bytes)
    (ROOT / 'inputs').mkdir(exist_ok=True)
    (ROOT / 'inputs' / 'SOURCE_STATE.json').write_bytes(state_bytes)
    input_root = ROOT / 'inputs' / 'B17_ROOT_BASE.json'
    shutil.copy2(child(prod, state['root']), input_root)
    if sha(input_root) != state['root_sha256']:
        raise ValueError('Snapshot base root bytes differ from accepted state')
    shutil.copy2(child(prod, state['cold_receipt']), ROOT / 'inputs' / 'BASE_COLD_REPLAY.json')
    old_cold = read(ROOT / 'inputs' / 'BASE_COLD_REPLAY.json')
    if old_cold['tree_sha256'] != state['root_sha256'] or old_cold['open'] != state['accepted_open']:
        raise ValueError('Prior full-root receipt differs from state')
    runtime = ROOT / 'runtime'
    shutil.copytree(prod / 'runtime', runtime, ignore=shutil.ignore_patterns('__pycache__'))
    sys.path.insert(0, str(runtime / 'v44'))
    import branch_protocol as bp
    if Path(bp.__file__).resolve() != runtime / 'v44' / 'branch_protocol.py' or bp.RULE != OLD_RULE:
        raise ValueError('Wrong original verifier import')
    (ROOT / 'candidates').mkdir()
    (ROOT / 'evidence').mkdir()
    accepted_ids = sorted(int(k) for k, r in state['cases'].items() if r['status'] == 'CLOSED')
    rows = {}
    # Existing production candidates are already strictly checked whole parents.
    for name, row in sorted(state['cases'].items(), key=lambda kv: int(kv[0])):
        if row['status'] != 'CANDIDATE':
            continue
        idx = int(name)
        result_file = child(prod, row['last_result'])
        source_record = result_file.parent / ('result_%07d.json' % idx)
        result, record = read(result_file), read(source_record)
        parent = read(child(prod, row['parent']))
        certificate = read(child(prod, row['certificate']))
        actual_sha = sha(child(prod, row['certificate']))
        if (row['certificate_sha256'] != actual_sha or result['certificate_sha256'] != actual_sha
                or result['parent_sha256'] != row['parent_sha256']
                or sha(child(prod, row['parent'])) != row['parent_sha256']
                or result['index'] != idx or result['complete'] is not True
                or result['status'] not in ('EMPTY', 'SAFE')
                or result['exact_receipt']['counts'].get('O', 0)):
            raise ValueError('Production candidate receipt identity/status differs: ' + name)
        if (record['index'] != idx or record['status'] != result['status']
                or record['node']['kind'] != 'B44' or record['node']['certificate'] != certificate
                or record['node']['parent'] != {k: parent[k] for k in KEYS}
                or record['path'] != parent['path'] or record['box'] != parent['box']
                or record['box_sha256'] != parent['box_sha256']):
            raise ValueError('Production strict graft record differs: ' + name)
        c = counts(certificate['tree'])
        if c.get('O', 0) or not equal_counts(c, result['counts']) or not equal_counts(c, result['exact_receipt']['counts']):
            raise ValueError('Production complete certificate counts differ: ' + name)
        if any(certificate.get(k) != value for k, value in bp.binding(parent).items()):
            raise ValueError('Production old V44 envelope differs: ' + name)
        target = ROOT / 'candidates' / source_record.name
        shutil.copy2(source_record, target)
        evidence = ROOT / 'evidence' / name
        evidence.mkdir()
        shutil.copy2(result_file, evidence / 'PRODUCTION_RESULT.json')
        rows[idx] = {'index': idx, 'origin': 'PRODUCTION_CANDIDATE', 'status': result['status'],
                     'counts': c, 'record_file': str(target.relative_to(ROOT)),
                     'record_file_sha256': sha(target), 'source_certificate_file_sha256': actual_sha,
                     'source_result': str(result_file), 'source_result_file_sha256': sha(result_file),
                     'source_parent_file_sha256': row['parent_sha256']}
        del parent, certificate, result, record

    old_source = (runtime / 'v44' / 'branch_protocol.py').read_text()
    expected_deep_source = old_source.replace("RULE='" + OLD_RULE + "'", "RULE='" + DEEP_RULE + "'", 1).replace('if depth>128:', 'if depth>500:', 1)
    deep_runtime = deep / 'runtime' / 'deep500' / 'v44'
    if ((deep_runtime / 'branch_protocol.py').read_text() != expected_deep_source
            or (deep_runtime / 'v44_bootstrap.py').read_bytes() != (runtime / 'v44' / 'v44_bootstrap.py').read_bytes()):
        raise ValueError('Deep verifier is not the exact rule/depth-only extension')
    expected_deep_identity = bp.json_hash({'rule': DEEP_RULE,
        'files': {n: sha(deep_runtime / n) for n in ('v44_bootstrap.py', 'branch_protocol.py')},
        'U41': bp.vp.rule_identity()})
    duplicates = []
    for strict_file in sorted((deep / 'parents').glob('*/STRICT_DEEP500_RESULT.json')):
        idx = int(strict_file.parent.name)
        strict = read(strict_file)
        if strict.get('status') != 'STRICT_DEEP500_PARENT_ACCEPTED':
            continue
        if str(idx) not in state['cases']:
            raise ValueError('Deep result is outside the fixed original parent universe')
        if idx in accepted_ids or idx in rows:
            duplicates.append(idx)
            continue
        coverage = read(strict_file.parent / 'COVERAGE.json')
        merged_file = strict_file.parent / 'MERGED.json'
        merged_sha = sha(merged_file)
        if (strict['merged_file_sha256'] != merged_sha or coverage['merged_file_sha256'] != merged_sha
                or strict['rule'] != DEEP_RULE or strict['rule_identity'] != expected_deep_identity):
            raise ValueError('Strict deep result identity differs: ' + str(idx))
        original = read(merged_file)
        ar = read(deep / 'anchors' / str(idx) / 'ANCHOR.json')
        parent = read(child(deep, ar['parent_file']))
        production_parent = read(child(prod, state['cases'][str(idx)]['parent']))
        if {k: parent[k] for k in KEYS} != {k: production_parent[k] for k in KEYS}:
            raise ValueError('Deep parent owner differs from production original')
        expect = dict(bp.binding(parent))
        expect.update(rule=DEEP_RULE, rule_identity=expected_deep_identity)
        if any(original.get(k) != value for k, value in expect.items()):
            raise ValueError('Deep envelope differs from paid actual parent')
        c = counts(original['tree'])
        exact = strict['exact_receipt']
        if (c.get('O', 0) or exact['status'] not in ('EMPTY', 'SAFE')
                or exact['index'] != idx or not equal_counts(c, exact['counts'])
                or digest(original) != strict['merged_sha256']):
            raise ValueError('Deep whole-parent completeness receipt differs')
        converted = bp.wrap(parent, original['tree'], original['profile'])
        if converted['tree'] != original['tree'] or converted['profile'] != original['profile']:
            raise ValueError('Identity rewrap changed the proof')
        record = {'index': idx, 'path': parent['path'], 'box': parent['box'],
                  'box_sha256': parent['box_sha256'], 'status': exact['status'],
                  'node': {'kind': 'B44', 'parent': {k: parent[k] for k in KEYS}, 'certificate': converted}}
        target = ROOT / 'candidates' / ('result_%07d.json' % idx)
        atomic(target, record)
        evidence = ROOT / 'evidence' / str(idx)
        evidence.mkdir()
        shutil.copy2(strict_file, evidence / 'SOURCE_STRICT_DEEP500_RESULT.json')
        shutil.copy2(merged_file, evidence / 'SOURCE_DEEP500_MERGED.json')
        shutil.copy2(strict_file.parent / 'COVERAGE.json', evidence / 'SOURCE_COVERAGE.json')
        conversion = {'status': 'IDENTITY_REWRAP_PENDING_ORIGINAL_FULL_ROOT_REPLAY', 'index': idx,
                      'source_deep_certificate_file_sha256': merged_sha,
                      'source_strict_receipt_file_sha256': sha(strict_file),
                      'source_rule': DEEP_RULE, 'source_rule_identity': expected_deep_identity,
                      'target_rule': OLD_RULE, 'target_rule_identity': bp.rule_hash(),
                      'actual_depth': c['maxdepth'], 'old_depth_limit': 128,
                      'same_tree_and_profile': True, 'new_certificate_sha256': digest(converted),
                      'new_record_file_sha256': sha(target),
                      'old_verifier_replay_already_performed': False,
                      'new_acceptance_will_be_original_full_fraction_root_replay': True}
        atomic(evidence / 'CONVERSION.json', conversion)
        rows[idx] = {'index': idx, 'origin': 'DEPTH500_COMPLETE_REBOUND_TO_ORIGINAL_V44',
                     'status': exact['status'], 'counts': c, 'record_file': str(target.relative_to(ROOT)),
                     'record_file_sha256': sha(target), 'source_strict_receipt_file_sha256': sha(strict_file),
                     'conversion_file': str((evidence / 'CONVERSION.json').relative_to(ROOT))}
        del original, converted, record, parent, production_parent
    if not rows:
        raise ValueError('No new complete parents to accept')
    remaining = sorted(int(k) for k in state['cases'] if int(k) not in accepted_ids and int(k) not in rows)
    if len(accepted_ids) + len(rows) + len(remaining) != len(state['cases']):
        raise ValueError('Snapshot parent accounting is incomplete')
    source_manifest_sha = sha(runtime / 'R54_SOURCE_MANIFEST.json')
    if source_manifest_sha != old_cold['source_manifest_sha256']:
        raise ValueError('Frozen source manifest changed since prior acceptance')
    result = {'schema': 'RHO5_INDEPENDENT_ORIGINAL_ROOT_ACCEPTANCE_SNAPSHOT_V1',
              'epoch': time.time(), 'source_root': str(prod), 'deep_source_root': str(deep),
              'source_generation': state['generation'], 'source_state_epoch': state.get('updated_epoch'),
              'source_state_file_sha256': hashlib.sha256(state_bytes).hexdigest(),
              'parent_root_sha256': state['root_sha256'], 'prior_accepted_open': state['accepted_open'],
              'already_formally_accepted_count': len(accepted_ids), 'already_formally_accepted_indices': accepted_ids,
              'new_complete_count': len(rows), 'new_complete_indices': sorted(rows),
              'production_candidate_count': sum(r['origin'] == 'PRODUCTION_CANDIDATE' for r in rows.values()),
              'deep_additional_count': sum(r['origin'] != 'PRODUCTION_CANDIDATE' for r in rows.values()),
              'deep_duplicate_indices': duplicates, 'remaining_unclosed_count': len(remaining),
              'remaining_unclosed_indices': remaining, 'total_parent_count': len(state['cases']),
              'candidates': [rows[k] for k in sorted(rows)], 'source_manifest_sha256': source_manifest_sha,
              'base_root_file': str(input_root.relative_to(ROOT)), 'base_root_bytes': input_root.stat().st_size,
              'candidate_record_bytes': sum((ROOT / r['record_file']).stat().st_size for r in rows.values()),
              'production_modified': False, 'formal_acceptance_pending': True}
    atomic(ROOT / 'SNAPSHOT.json', result)
    atomic(ROOT / 'INPUT_MANIFEST.json', {'runner_file_sha256': sha(__file__),
        'snapshot_file_sha256': sha(ROOT / 'SNAPSHOT.json'), 'base_root_file_sha256': state['root_sha256'],
        'base_cold_receipt_file_sha256': sha(ROOT / 'inputs' / 'BASE_COLD_REPLAY.json'),
        'frozen_runtime_manifest_file_sha256': source_manifest_sha,
        'candidate_records': {r['record_file']: r['record_file_sha256'] for r in rows.values()}})
    gc.collect()
    return result


def status(phase, **fields):
    atomic(ROOT / 'STATUS.json', {'phase': phase, 'epoch': time.time(), 'pid': os.getpid(),
                                 'production_modified': False, 'model_wakeups': False, **fields})


def run_stage(name, command, config, limits):
    log_path = ROOT / (name + '.log')
    with log_path.open('ab') as log:
        proc = subprocess.Popen(list(map(str, command)), cwd=ROOT, stdin=subprocess.DEVNULL,
                                stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        began = time.time()
        try:
            while proc.poll() is None:
                pss, pids = task_memory(proc.pid)
                available = memory_available()
                status(name, stage_pid=proc.pid, stage_started_epoch=began, limits=limits,
                       total_task_pss_bytes=pss, mem_available_bytes=available, owned_processes=pids,
                       pss_available=pss is not None,
                       log_file=str(log_path.relative_to(ROOT)))
                if (ROOT / 'STOP.json').exists():
                    raise RuntimeError('Explicit stop of this acceptance task')
                if pss is not None and pss > config['total_task_pss_gib'] * GIB:
                    raise MemoryError('Total acceptance-task PSS exceeded its 32 GiB guard')
                if available < config['system_reserve_gib'] * GIB:
                    raise MemoryError('System available memory entered its 8 GiB reserve')
                if shutil.disk_usage(ROOT).free < config['disk_reserve_gib'] * GIB:
                    raise OSError('Acceptance task disk reserve guard')
                time.sleep(5)
            if proc.returncode:
                raise RuntimeError(name + ' failed, code ' + str(proc.returncode) + '; see ' + str(log_path))
        except BaseException:
            # The pool can outlive an abnormally exited stage parent. Signal
            # this stage's dedicated group even if its leader already exited.
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            if proc.poll() is None:
                try:
                    proc.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
            raise


def validate_acceptance(snap, limits):
    old = read(ROOT / 'inputs' / 'BASE_COLD_REPLAY.json')
    graft = read(ROOT / 'checkpoint' / 'APPLY_RECEIPT.json')
    cold = read(ROOT / 'COLD_REPLAY.json')
    root_sha = sha(ROOT / 'checkpoint' / 'B17_ROOT.json')
    if (graft['parent_tree_sha256'] != snap['parent_root_sha256']
            or root_sha != graft['tree_sha256'] or root_sha != cold['tree_sha256']
            or cold['backend'] != 'fraction' or cold['workers'] != limits['workers']):
        raise ValueError('Full Fraction root/input/worker binding mismatch')
    added = snap['new_complete_count']
    if (cold['nodes'] != old['nodes'] or cold['splits'] != old['splits']
            or cold['max_depth'] != old['max_depth']
            or cold['open'] != snap['prior_accepted_open'] - added
            or cold['open'] != snap['remaining_unclosed_count']
            or cold['kinds'] != graft['kinds']
            or cold['contradictions'] + cold['alpha_safe'] + cold['open'] != cold['splits'] + 1):
        raise ValueError('Whole-root structural or completeness counts mismatch')
    for k in ('model_sha256', 'r54_binding', 'source_manifest_sha256'):
        if cold[k] != old[k]:
            raise ValueError('Original frozen model/rule identity changed: ' + k)
    if {x['index'] for x in graft['applied']} != set(snap['new_complete_indices']):
        raise ValueError('Not exactly the snapshotted complete parents were grafted')
    if cold['contradictions'] != old['contradictions'] + sum(r['status'] == 'EMPTY' for r in snap['candidates']):
        raise ValueError('Contradiction increment mismatch')
    if cold['alpha_safe'] != old['alpha_safe'] + sum(r['status'] == 'SAFE' for r in snap['candidates']):
        raise ValueError('Safe increment mismatch')
    total = Counter()
    for r in snap['candidates']:
        total.update(r['counts'])
    before, after = old['terminal_audit'], cold['terminal_audit']
    for key in ('nodes', 'S', 'C', 'I', 'H', 'A', 'O', 'new_waves', 'new_bounds'):
        if after.get('B44_local_' + key, 0) - before.get('B44_local_' + key, 0) != total[key]:
            raise ValueError('Detailed B44 receipt increment mismatch: ' + key)
    if after['B44_local_O'] != 0 or cold['kinds']['B44'] != old['kinds']['B44'] + added:
        raise ValueError('Incomplete or duplicate B44 parent acceptance')
    for key, value in before.items():
        if key.startswith('U41_') and after.get(key) != value:
            raise ValueError('Old U41 coverage changed')
    for key, value in after.items():
        if key.endswith('_dense_crosschecks') and value != after[key.replace('_dense_crosschecks', '_bounds')]:
            raise ValueError('Missing mandatory dense crosschecks')
    result = {'status': 'ORIGINAL_FULL_FRACTION_ROOT_ACCEPTED_ADOPTION_READY', 'epoch': time.time(),
              'snapshot_file_sha256': sha(ROOT / 'SNAPSHOT.json'),
              'root_file': 'checkpoint/B17_ROOT.json', 'root_sha256': root_sha,
              'cold_receipt_file': 'COLD_REPLAY.json', 'cold_receipt_file_sha256': sha(ROOT / 'COLD_REPLAY.json'),
              'apply_receipt_file_sha256': sha(ROOT / 'checkpoint' / 'APPLY_RECEIPT.json'),
              'source_generation': snap['source_generation'], 'source_parent_root_sha256': snap['parent_root_sha256'],
              'accepted_new_indices': snap['new_complete_indices'], 'accepted_new_count': added,
              'previous_formally_accepted_count': snap['already_formally_accepted_count'],
              'now_formally_proved_parent_count': snap['already_formally_accepted_count'] + added,
              'remaining_unclosed_indices': snap['remaining_unclosed_indices'],
              'remaining_unclosed_count': cold['open'], 'total_parent_count': snap['total_parent_count'],
              'workers': cold['workers'], 'cold_replay_seconds': cold['seconds'],
              'old_frozen_rule_unchanged': True, 'old_math_replays_before_full_root': 0,
              'production_STATE_adopted': False, 'production_modified': False,
              'whole_B_closed': cold['whole_B_closed'], 'macro_ledger': '14/15',
              'adoption_rule': ('Production sole state owner must compare-and-swap source root/generation, '
                                'reconcile newer case outcomes, then adopt this root and receipt. '
                                'Never overwrite the live STATE from this background task.')}
    atomic(ROOT / 'ACCEPTANCE.json', result)
    atomic(ROOT / 'ADOPTION_READY.json', result)
    return result


def run(config):
    if (ROOT / 'RUN_STARTED.json').exists():
        raise ValueError('This immutable acceptance job has already started; no implicit second replay')
    atomic(ROOT / 'RUN_STARTED.json', {'epoch': time.time(), 'pid': os.getpid()})
    def on_signal(signum, _frame):
        raise RuntimeError('Acceptance runner received stop signal ' + str(signum))
    signal.signal(signal.SIGTERM, on_signal)
    signal.signal(signal.SIGINT, on_signal)
    try:
        limits = configure(config)
        atomic(ROOT / 'RESOURCE_LIMITS.json', limits)
        if shutil.disk_usage(ROOT).free < 12 * GIB:
            raise OSError('Need at least 12 GiB free disk before snapshot')
        status('PREPARING_IMMUTABLE_SNAPSHOT', limits=limits)
        snap = snapshot(config)
        status('SNAPSHOT_READY', snapshot={k: snap[k] for k in (
            'already_formally_accepted_count', 'new_complete_count', 'production_candidate_count',
            'deep_additional_count', 'remaining_unclosed_count', 'candidate_record_bytes')}, limits=limits)
        run_stage('APPLYING_ORIGINAL_ROOT', [sys.executable, '-B', '-S', ROOT / 'runtime' / 'r54_apply.py',
                  '--tree', ROOT / 'inputs' / 'B17_ROOT_BASE.json', '--results', ROOT / 'candidates',
                  '--out', ROOT / 'checkpoint'], config, limits)
        run_stage('FULL_FRACTION_REPLAY', [sys.executable, '-B', '-S', ROOT / 'runtime' / 'r54_replay.py',
                  '--tree', ROOT / 'checkpoint' / 'B17_ROOT.json', '--out', ROOT / 'COLD_REPLAY.json',
                  '--backend', 'fraction', '--workers', str(limits['workers']), '--allow-open'], config, limits)
        result = validate_acceptance(snap, limits)
        status('ACCEPTED_ADOPTION_READY', acceptance=result, limits=limits)
        print(json.dumps(result, sort_keys=True), flush=True)
    except BaseException:
        error = {'status': 'ERROR_SAVED', 'epoch': time.time(), 'pid': os.getpid(),
                 'error': traceback.format_exc(), 'checkpoints_and_logs_preserved': True,
                 'automatic_retry': False, 'production_modified': False}
        atomic(ROOT / 'ERROR.json', error)
        status('ERROR_SAVED', error=error)
        raise


def main():
    p = argparse.ArgumentParser()
    p.add_argument('mode', choices=('launch', 'run', 'status'))
    p.add_argument('--source-root', default=DEFAULT_PROD)
    p.add_argument('--deep-root', default=DEFAULT_DEEP)
    p.add_argument('--workers', type=int, default=8)
    a = p.parse_args()
    if a.mode == 'status':
        print(json.dumps(read(ROOT / 'STATUS.json'), sort_keys=True))
        return
    if not 1 <= a.workers <= 8:
        p.error('Worker count must be 1 through 8')
    if a.mode == 'run':
        return run(read(ROOT / 'CONFIG.json'))
    if (ROOT / 'LAUNCH.json').exists() or (ROOT / 'RUN_STARTED.json').exists():
        raise ValueError('Refuse duplicate independent acceptance launch')
    if not ROOT.is_relative_to(Path('/root/microscope_ws')):
        raise ValueError('Heavy acceptance must launch only inside X task workspace')
    config = {'schema': 'RHO5_INDEPENDENT_ORIGINAL_ROOT_ACCEPTANCE_V1',
              'source_root': str(Path(a.source_root).resolve()), 'deep_root': str(Path(a.deep_root).resolve()),
              'workers': a.workers, 'cpu_cap': 8, 'process_memory_gib': 32, 'total_task_pss_gib': 32,
              'main_memory_reserve_gib': 24, 'worker_memory_reserve_gib': 1,
              'system_reserve_gib': 8, 'disk_reserve_gib': 6,
              'single_math_cold_replay': True, 'production_modified': False, 'model_wakeups': False}
    atomic(ROOT / 'CONFIG.json', config)
    with (ROOT / 'RUNNER.log').open('ab') as log:
        proc = subprocess.Popen([sys.executable, '-B', str(Path(__file__).resolve()), 'run'],
                                cwd=ROOT, stdin=subprocess.DEVNULL, stdout=log,
                                stderr=subprocess.STDOUT, start_new_session=True)
    launch = {'status': 'INDEPENDENT_ACCEPTANCE_LAUNCHED', 'epoch': time.time(), 'pid': proc.pid,
              'root': str(ROOT), 'production_modified': False, 'model_wakeups': False}
    atomic(ROOT / 'LAUNCH.json', launch)
    print(json.dumps(launch, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
