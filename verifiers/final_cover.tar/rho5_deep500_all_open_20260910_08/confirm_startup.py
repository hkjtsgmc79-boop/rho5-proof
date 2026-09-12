"""One bounded deployment observation, without mathematical replay."""
from pathlib import Path
import hashlib
import json
import sys
import time
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from coordinator import process_info, alive
from fast_checkpoint import atomic_json
from deep_math import file_sha

def read(p):
    return json.loads(Path(p).read_text())

if __name__ == '__main__':
    status, state, config = (read(ROOT / x) for x in ('STATUS.json', 'RUN_STATE.json', 'CONFIG.json'))
    launch = read(ROOT / 'LAUNCH.json')
    info = process_info(launch['pid'])
    if not info or info['state'] in ('Z', 'X') or info['start_ticks'] != str(launch['start_ticks']):
        raise ValueError('Coordinator is not running')
    source = Path(config['source_root'])
    current = read(source / 'STATE.json')['cases']
    unclosed = {k for k, v in current.items() if v.get('counts', {}).get('O', 0)}
    if not unclosed <= set(state['parents']):
        raise ValueError('Current unclosed parent absent from scope')
    if any('ERROR' in t['status'] for t in state['tasks'].values()) or (ROOT / 'DAEMON_ERROR.json').exists():
        raise ValueError('Deployment has recorded errors')
    manifest = read(ROOT / 'runtime/DEEP500_MANIFEST.json')
    if file_sha(source / 'runtime/v44/branch_protocol.py') != manifest['legacy_files']['branch_protocol.py']:
        raise ValueError('Original production verifier bytes changed')
    active = []
    for task in state['tasks'].values():
        if task['status'] != 'RUNNING' or not alive(task):
            continue
        req = read(ROOT / task['folder'] / 'TASK.json')
        if (req['max_depth'], req['milestone_depth'], req['periodic_restart']) != (500, 300, False):
            raise ValueError('Worker depth/continuity configuration differs')
        proc = Path('/proc') / str(task['pid'])
        stat = (proc / 'stat').read_text().rsplit(')', 1)[1].split()
        if int(stat[16]) < 10:
            raise ValueError('Worker nice priority differs')
        env = dict(part.split(b'=', 1) for part in (proc / 'environ').read_bytes().split(b'\0') if b'=' in part)
        if any(env.get(k.encode()) != b'1' for k in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS')):
            raise ValueError('Worker library thread configuration differs')
        progress_path = ROOT / task['folder'] / 'PROGRESS.json'
        progress = read(progress_path) if progress_path.exists() else {}
        active.append({'task_id': task['task_id'], 'index': task['index'], 'pid': task['pid'],
            'target_depth': len(task['target_path']), 'maxdepth': progress.get('maxdepth'),
            'current_path_depth': len(progress.get('current_path', '')), 'phase': progress.get('phase'),
            'cpu_seconds': progress.get('cpu_seconds'), 'checkpoint_bytes': progress.get('checkpoint_bytes'),
            'source_completed_epoch': req['source_completed_epoch']})
    if not active:
        raise ValueError('No search worker running')
    replacement = read(ROOT / 'SUPERVISOR_REPLACEMENT.json')
    continuity = []
    for key, old in replacement['workers_before'].items():
        now = state['tasks'][key]
        if now.get('pid') != old['pid'] or str(now.get('start_ticks')) != str(old['start_ticks']):
            raise ValueError('Deployment restarted a pre-existing search')
        continuity.append({'task_id': key, 'same_recorded_pid': True, 'current_status': now['status']})
    payload = {'status': 'DEPLOYMENT_RUNNING_CONFIRMED', 'epoch': time.time(),
        'daemon_pid': launch['pid'], 'currently_unclosed_source_parents': sorted(map(int, unclosed)),
        'all_current_unclosed_parents_in_scope': True, 'anchored_parents': len(state['parents']),
        'original_open_branches': len(state['tasks']), 'status_snapshot_epoch': status['epoch'],
        'task_status_counts': status['statuses'], 'active_workers_observed': active,
        'active_worker_count': len(active), 'capacity': status['capacity'],
        'deep100_workers_observed': [a for a in active if a['target_depth'] >= 100],
        'preexisting_search_continuity': continuity,
        'original_verifier_unchanged': True, 'new_rule_identity': read(ROOT / 'MATH_CHECKS.json')['new_rule_identity'],
        'old_large_math_replays_for_startup': 0, 'model_wakeups': False,
        'runtime_manifest_file_sha256': file_sha(ROOT / 'runtime/DEEP500_MANIFEST.json'),
        'support_files': {p.name: file_sha(p) for p in sorted(ROOT.glob('*.py'))},
        'closed_at_acceptance_still_open_in_production': status['closed_still_open_in_production_at_acceptance']}
    atomic_json(ROOT / 'DEPLOYMENT_CONFIRMED.json', payload)
    print(json.dumps({k: v for k, v in payload.items() if k not in ('support_files', 'capacity', 'active_workers_observed', 'preexisting_search_continuity')}, sort_keys=True))
