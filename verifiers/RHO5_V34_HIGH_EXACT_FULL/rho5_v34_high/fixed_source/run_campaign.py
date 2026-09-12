#!/usr/bin/env python3
"""40-worker, checkpointed discovery. Only exact original-root replay gives credit.
The model JSON files are immutable. Each worker owns an original-root envelope.
This script does not connect to a server or assume any particular host paths.
"""
from pathlib import Path
import sys,json,argparse,os,time,subprocess,shutil,hashlib
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'discovery'))
import frontier_parallel as fp
from build_models import make_model,headers
EXACT=('mc_exact_kernel.hpp','rankone_oracle.hpp','factor_graph.hpp','factor_oracle.hpp','mc_verify.cpp')
DISCOVERY=('discover_hybrid.cpp','fast_simplex.hpp','proposal_simplex.hpp')

def prepare(name):
 d=ROOT/'models'/name;data=json.loads((d/'model.json').read_text());re=make_model(data['K'],data['J'],data['type'],data['branch'])
 if re!=data:raise ValueError('semantic frozen model mismatch '+name)
 b=d/'build';b.mkdir(exist_ok=True);headers(data,b)
 for n in EXACT:shutil.copy2(ROOT/'source'/n,b/n)
 for n in DISCOVERY:shutil.copy2(ROOT/'discovery'/n,b/n)
 inputs=[b/n for n in EXACT+DISCOVERY+('mc_exact_model.hpp','mc_model.hpp')]
 h=hashlib.sha256(b''.join(p.read_bytes()for p in inputs)).hexdigest();cache=b/'compile.sha256'
 if not cache.exists()or cache.read_text()!=h or not(d/'verify').exists()or not(d/'discover_focus').exists():
  for src,exe in [('mc_verify.cpp',d/'verify'),('discover_hybrid.cpp',d/'discover_focus')]:
   r=subprocess.run(['g++','-O3','-std=c++17',src,'-o',str(exe)],cwd=b,text=True,capture_output=True)
   (b/(src+'.compile.log')).write_text(r.stdout+r.stderr)
   if r.returncode:raise RuntimeError(r.stderr)
  cache.write_text(h)
 return fp.digest(d/'model.json')

def main():
 available=sorted(d.name for d in(ROOT/'models').iterdir()if(d/'model.json').exists())
 p=argparse.ArgumentParser();p.add_argument('--models',nargs='+',choices=available,default=available)
 p.add_argument('--workers',type=int,default=40);p.add_argument('--seconds',type=float,default=7200)
 p.add_argument('--chunk',type=float,default=120);p.add_argument('--wave-seconds',type=float,default=600)
 p.add_argument('--frontiers',type=int,default=80);p.add_argument('--output',type=Path,default=ROOT/'campaign')
 p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 if not 1<=a.workers<=40:raise ValueError('workers must be 1..40')
 if min(a.seconds,a.chunk,a.wave_seconds)<=0:raise ValueError('positive budgets required')
 for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
 if hasattr(os,'setpriority'):
  try:
   if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
  except PermissionError:pass
 # Respect inherited CPLUS_INCLUDE_PATH/TMPDIR; never inject someone else's path.
 out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
 fp.PINS={n:prepare(n)for n in a.models}
 current=out/'CURRENT_STATE.json';accepted={}
 if current.exists():
  state=json.loads(current.read_text());accepted=state['models']
  for n,v in accepted.items():
   if n not in fp.PINS:raise ValueError('use same model set for a continued campaign')
   if fp.digest(v['tree'])!=v['tree_sha256']or v['model_sha256']!=fp.PINS[n]:raise ValueError('checkpoint/model hash mismatch')
 inputs={}
 for n in a.models:
  if n in accepted:
   if accepted[n]['open']>0:inputs[n]=Path(accepted[n]['tree'])
  else:
   d=ROOT/'models'/n;cp=d/'checkpoint.tree'
   if not cp.exists():
    if(d/'checkpoint.tree.gz').exists():
     import gzip
     with gzip.open(d/'checkpoint.tree.gz','rb')as f,cp.open('wb')as g:shutil.copyfileobj(f,g)
    else:cp.write_text('O\n')
   fp.run_verify(d/'verify',cp);inputs[n]=cp
 if a.prepare_only:
  print(json.dumps({'status':'PREPARED_NOT_PROVED','models':fp.PINS}));return
 deadline=time.monotonic()+a.seconds;index=len(list(out.glob('wave_*')))
 while inputs and time.monotonic()<deadline:
  index+=1;wave=out/f'wave_{index:04d}'
  jobs,manifest=fp.prepare_wave(ROOT,wave,inputs,max(a.frontiers,2*a.workers))
  print(json.dumps({'event':'wave_prepared','wave':index,'frontiers':len(jobs),'workers':a.workers}),flush=True)
  fp.execute_wave(ROOT,wave,jobs,a.workers,min(deadline,time.monotonic()+a.wave_seconds),a.chunk)
  result=fp.graft_wave(ROOT,wave,jobs,manifest);accepted.update(result)
  fp.write_json(current,{'status':'COMPLETE_SELECTED_ORIGINAL_ROOTS'if len(accepted)==len(a.models)and all(v['open']==0 for v in accepted.values())else'EXACT_PARTIAL_ORIGINAL_ROOTS','models':accepted,'workers_cap':a.workers,'ledger':'11/15'})
  print(json.dumps({'event':'original_roots_accepted','wave':index,'models':{n:{k:v[k]for k in('nodes','leaves','open','max_depth','full_factor_leaves')}for n,v in result.items()}}),flush=True)
  inputs={n:Path(v['tree'])for n,v in accepted.items()if v['open']>0}
  if(out/'STOP_AFTER_WAVE').exists():break
 complete=len(accepted)==len(a.models)and all(v['open']==0 for v in accepted.values())
 print(json.dumps({'status':'SELECTED_ROOTS_COMPLETE'if complete else'BUDGET_CHECKPOINTS_SAVED_NOT_A_HEIGHT_PROOF','state':str(current),'whole_R':'OPEN','macro_ledger':'11/15'}),flush=True)
if __name__=='__main__':
 import fcntl
 with (ROOT/'.campaign.lock').open('a') as lock:
  try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
  except BlockingIOError:raise SystemExit('Another campaign is using this package; do not run two writers.')
  main()
