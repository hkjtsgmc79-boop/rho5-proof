#!/usr/bin/env python3
"""Launch the authorized owned X campaign independent of a quiet SSH channel."""
from pathlib import Path
import subprocess,json,os,sys,datetime,fcntl
root=Path('/root/microscope_ws/rho5_cqg_v35_low_alpha_20260908/attempt_01')
work=root/'working_flow_tube'
lock=(work/'.campaign.lock').open('a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
log=root/'FLOW_TUBE_CAMPAIGN_01.log'
assert not log.exists(),'Do not silently start a duplicate campaign'
env=os.environ.copy();env.update(CPLUS_INCLUDE_PATH='/root/microscope_ws/controller_v31_review_20260907.cRz00v/deps/usr/include',
    TMPDIR=str(root/'tmp'),OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1')
cmd=['nice','-n','10',sys.executable,'run_campaign.py','--models','I_LOW_ALPHA','II_LOW_ALPHA',
     '--workers','40','--seconds','7200','--chunk','120','--wave-seconds','600','--frontiers','160','--output','campaign_low_alpha']
lock.close()
with log.open('w') as f:
    p=subprocess.Popen(cmd,cwd=work,env=env,stdin=subprocess.DEVNULL,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
receipt={'status':'AUTHORIZED_FLOW_CAMPAIGN_DISPATCHED','pid':p.pid,'cwd':str(work),'command':cmd,
         'log':str(log),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'workers_cap':40,
         'note':'Dispatch is not mathematical completion. Check original-root state and final cold replay.'}
(root/'FLOW_TUBE_LAUNCH.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
