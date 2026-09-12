#!/usr/bin/env python3
"""Bounded one-time pipeline: finish current strict campaign, then build real archives."""
from pathlib import Path
import json,sys,os,subprocess,time,fcntl,datetime,hashlib
own=Path('/root/microscope_ws/rho5_cqg_v35_low_alpha_20260908/attempt_01')
work=own/'working_weighted_height';dest=own/'delivery_final'
def status(kind,**extra):
 d={'status':kind,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**extra}
 p=own/'FINALIZATION_STATUS.json';tmp=p.with_suffix('.next');tmp.write_text(json.dumps(d,indent=2)+'\n');os.replace(tmp,p)
 print(json.dumps(d),flush=True)
def run():
 # Set the absolute target once, rather than adding two nice increments.
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 with (own/'.finalization_pipeline.lock').open('a') as single:
  fcntl.flock(single,fcntl.LOCK_EX|fcntl.LOCK_NB)
  status('WAITING_FOR_COMPLETE_STRICT_CAMPAIGN',nice=os.getpriority(os.PRIO_PROCESS,0),
         package=str(work),deadline_seconds=7200)
  deadline=time.monotonic()+7200
  with (work/'.campaign.lock').open('a') as lock:
   while True:
    try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);break
    except BlockingIOError:
     if time.monotonic()>=deadline:raise TimeoutError('Current campaign has not finished within the bounded wait')
     time.sleep(5)
   state=json.loads((work/'campaign_low_alpha/CURRENT_STATE.json').read_text())
   if set(state['models'])!={'I_LOW_ALPHA','II_LOW_ALPHA'}:raise ValueError('Wrong model set')
   if any(v['open']!=0 for v in state['models'].values()):raise ValueError('Campaign stopped with unpaid roots; resume research before final export')
   if not all(v.get('original_root_accepted') for v in state['models'].values()):raise ValueError('Missing full original-root acceptance')
   if dest.exists():raise FileExistsError('Final destination already exists; inspect it instead of overwriting')
   status('BUILDING_REAL_FINAL_DELIVERY',package=str(work),destination=str(dest),
          complete_root_counts={n:{k:v[k] for k in ('nodes','contradiction_leaves','alpha_safe_leaves','weighted_height_leaves','open')} for n,v in state['models'].items()})
   env=os.environ.copy();env.update(OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1',
    TMPDIR=str(own/'tmp'),CPLUS_INCLUDE_PATH='/root/microscope_ws/controller_v31_review_20260907.cRz00v/deps/usr/include')
   with (own/'FINAL_DELIVERY_BUILD.log').open('w') as log:
    p=subprocess.run([sys.executable,str(own/'make_final_delivery.py'),'--package',str(work),'--out',str(dest)],
                     env=env,stdout=log,stderr=subprocess.STDOUT)
   if p.returncode:raise RuntimeError('Final builder failed; inspect FINAL_DELIVERY_BUILD.log')
   receipt=json.loads((dest/'DELIVERY_RECEIPT.json').read_text())
   if receipt['status']!='COMPLETE_TWO_ROOT_ALPHA_DELIVERY':raise ValueError('Unexpected partial final delivery')
   status('REAL_FINAL_DELIVERY_READY_ON_X_LOCAL_DOWNLOAD_STILL_REQUIRED',
          receipt=str(dest/'DELIVERY_RECEIPT.json'),receipt_sha256=hashlib.sha256((dest/'DELIVERY_RECEIPT.json').read_bytes()).hexdigest(),
          full=receipt['full'],light=receipt['light'],report=receipt['report'])
if '--run' in sys.argv:
 try:run()
 except Exception as e:
  status('FINALIZATION_FAILED_REVIEW_REQUIRED',error=str(e));raise
else:
 log=own/'FINALIZATION_PIPELINE.log'
 with log.open('x') as f:
  p=subprocess.Popen([sys.executable,str(Path(__file__).resolve()),'--run'],cwd=own,
   stdin=subprocess.DEVNULL,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
 rec={'status':'ONE_TIME_FINALIZATION_PIPELINE_LAUNCHED','pid':p.pid,'log':str(log),
      'package':str(work),'destination':str(dest),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'requires_complete_strict_campaign_before_export':True,'local_download_not_performed':True}
 (own/'FINALIZATION_LAUNCH.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
