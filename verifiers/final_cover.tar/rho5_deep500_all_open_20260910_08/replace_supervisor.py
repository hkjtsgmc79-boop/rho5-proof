"""One deployment-time supervisor replacement; running searches are untouched."""
from pathlib import Path
import json
import os
import signal
import subprocess
import sys
import time
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from launch import process_identity, atomic

if __name__ == '__main__':
    record = json.loads((ROOT / 'LAUNCH.json').read_text())
    identity = process_identity(record['pid'])
    if not identity or not identity['alive'] or not identity['same_coordinator'] or identity['start_ticks'] != str(record['start_ticks']):
        raise RuntimeError('Refuse replacing an unmatched supervisor')
    for name in ('coordinator.py', 'source_inputs.py', 'parents_merger.py'):
        compile((ROOT / name).read_text(), str(ROOT / name), 'exec')
    # Freeze only the coordinator, leaving all branch and merger processes running.
    os.kill(record['pid'], signal.SIGSTOP)
    try:
        state = json.loads((ROOT / 'RUN_STATE.json').read_text())
        workers = {k: {'pid': t.get('pid'), 'start_ticks': t.get('start_ticks')}
                   for k, t in state['tasks'].items() if t['status'] == 'RUNNING'}
        atomic(ROOT / 'SUPERVISOR_REPLACEMENT.json', {'epoch': time.time(),
            'old_supervisor': record, 'workers_before': workers,
            'search_processes_signaled': False,
            'reason': 'Deployment completion: prioritize formerly capped branches and enforce disk reserve'})
    except BaseException:
        os.kill(record['pid'], signal.SIGCONT)
        raise
    # The persisted state plus /proc adoption keeps ownership across this replacement.
    os.kill(record['pid'], signal.SIGKILL)
    end = time.monotonic() + 3
    while time.monotonic() < end:
        current = process_identity(record['pid'])
        if not current or not current['alive']:
            break
        time.sleep(0.05)
    result = subprocess.run([sys.executable, '-B', str(ROOT / 'launch.py')], check=False,
                            capture_output=True, text=True)
    print(result.stdout, end='')
    print(result.stderr, end='', file=sys.stderr)
    raise SystemExit(result.returncode)
