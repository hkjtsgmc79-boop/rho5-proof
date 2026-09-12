#!/usr/bin/env python3
"""Launch the new exact rule version after complete, hash-bound adoption."""
from pathlib import Path
import json,subprocess,os,sys,fcntl,datetime,hashlib,argparse
ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=int,default=7200);a=ap.parse_args();assert a.seconds>0
own=Path('/root/microscope_ws/rho5_cqg_v35_low_alpha_20260908/attempt_01');work=own/'working_weighted_height'
oldlock=(own/'working_flow_tube/.campaign.lock').open('a');fcntl.flock(oldlock,fcntl.LOCK_EX|fcntl.LOCK_NB)
lock=(work/'.campaign.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
adopt=json.loads((own/'WEIGHTED_HEIGHT_ADOPTION.json').read_text())
assert adopt['status']=='LATEST_TWO_ORIGINAL_ROOTS_ADOPTED_I_REPROVED_II_NEW_REPLAY_REQUIRED'
state=json.loads((work/'campaign_low_alpha/CURRENT_STATE.json').read_text())
assert set(state['models'])=={'I_LOW_ALPHA','II_LOW_ALPHA'}
assert any(v['open']>0 for v in state['models'].values()),'Already complete'
stop=work/'campaign_low_alpha/STOP_AFTER_WAVE'
if stop.exists():stop.unlink()
index=max([int(p.stem.rsplit('_',1)[1]) for p in own.glob('WEIGHTED_HEIGHT_CAMPAIGN_*.log')]+[0])+1
log=own/f'WEIGHTED_HEIGHT_CAMPAIGN_{index:02d}.log'
env=os.environ.copy();env.update(OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1',
 CPLUS_INCLUDE_PATH='/root/microscope_ws/controller_v31_review_20260907.cRz00v/deps/usr/include',TMPDIR=str(own/'tmp'))
cmd=['nice','-n','10',sys.executable,'run_campaign.py','--models','I_LOW_ALPHA','II_LOW_ALPHA',
     '--workers','40','--seconds',str(a.seconds),'--chunk','120','--wave-seconds','1200','--frontiers','160','--output','campaign_low_alpha']
lock.close()
with log.open('w') as f:
 p=subprocess.Popen(cmd,cwd=work,env=env,stdin=subprocess.DEVNULL,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
receipt={'status':'WEIGHTED_HEIGHT_SAME_ROOTS_CAMPAIGN_LAUNCHED','pid':p.pid,'command':cmd,'log':str(log),
         'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'cwd':str(work),
         'starting_open':{n:v['open'] for n,v in state['models'].items()},
         'source_manifest_sha256':hashlib.sha256((work/'MANIFEST.json').read_bytes()).hexdigest(),
         'mathematical_completion':False}
(own/f'WEIGHTED_HEIGHT_LAUNCH_{index:02d}.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
