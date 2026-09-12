#!/usr/bin/env python3
"""Resume the same accepted two roots without depending on an idle SSH session."""
from pathlib import Path
import subprocess,json,os,sys,datetime,fcntl,argparse,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=int,default=6600)
ap.add_argument('--wave-seconds',type=int,default=600);a=ap.parse_args()
assert a.seconds>0 and a.wave_seconds>0
own=Path('/root/microscope_ws/rho5_cqg_v35_low_alpha_20260908/attempt_01');work=own/'working_flow_tube'
lock=(work/'.campaign.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
state=json.loads((work/'campaign_low_alpha/CURRENT_STATE.json').read_text())
assert set(state['models'])=={'I_LOW_ALPHA','II_LOW_ALPHA'}
assert any(v['open']>0 for v in state['models'].values()),'Already complete'
pause=work/'campaign_low_alpha/STOP_AFTER_WAVE'
if pause.exists():pause.unlink()
index=max([int(p.stem.rsplit('_',1)[1]) for p in own.glob('FLOW_TUBE_CAMPAIGN_*.log')]+[0])+1
log=own/f'FLOW_TUBE_CAMPAIGN_{index:02d}.log'
env=os.environ.copy();env.update(CPLUS_INCLUDE_PATH='/root/microscope_ws/controller_v31_review_20260907.cRz00v/deps/usr/include',
 TMPDIR=str(own/'tmp'),OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1')
# run_campaign sets nice=10 from a normal-priority launch; avoid adding nice twice.
cmd=[sys.executable,'run_campaign.py','--models','I_LOW_ALPHA','II_LOW_ALPHA',
     '--workers','40','--seconds',str(a.seconds),'--chunk','120','--wave-seconds',str(a.wave_seconds),'--frontiers','160','--output','campaign_low_alpha']
lock.close()
with log.open('w') as f:
 p=subprocess.Popen(cmd,cwd=work,env=env,stdin=subprocess.DEVNULL,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
record={'status':'SAME_ORIGINAL_ROOTS_RESUMED','pid':p.pid,'cwd':str(work),'command':cmd,'log':str(log),
        'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'starting_open':{n:v['open'] for n,v in state['models'].items()},
        'discovery_source_sha256':hashlib.sha256((work/'discovery/frontier_parallel.py').read_bytes()).hexdigest(),
        'mathematical_completion':False}
(own/f'FLOW_TUBE_LAUNCH_{index:02d}.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
