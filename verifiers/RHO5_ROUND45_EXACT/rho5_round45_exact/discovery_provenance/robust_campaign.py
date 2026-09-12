"""Resume frozen original roots using repaired numerical proposals and exact grafting."""
from pathlib import Path
import argparse, json, os, subprocess, time
import frontier_parallel as fp

def main():
 ap=argparse.ArgumentParser();ap.add_argument('task_root',type=Path)
 ap.add_argument('--model',choices=list(fp.PINS),default='II210_214')
 ap.add_argument('--workers',type=int,default=4);ap.add_argument('--seconds',type=float,default=600)
 ap.add_argument('--chunk',type=float,default=120);ap.add_argument('--wave-seconds',type=float,default=600)
 a=ap.parse_args();root=a.task_root.resolve();work=root/'working';model=work/'models'/a.model
 out=root/('parallel_robust_'+a.model);out.mkdir(exist_ok=True)
 assert 1<=a.workers<=40
 for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
 os.environ['TMPDIR']=str(root/'tmp');os.environ['CPLUS_INCLUDE_PATH']='/root/microscope_ws/controller_v31_review_20260907.cRz00v/deps/usr/include'
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 receipt=json.loads((root/'robust_proposal/DISCOVERY_REPAIR_RECEIPT.json').read_text())
 assert fp.digest(model/'model.json')==fp.PINS[a.model]
 proposal=root/'robust_proposal'/a.model
 assert fp.digest(proposal/'discover_robust.cpp')==receipt['source_sha256']
 assert fp.digest(proposal/'proposal_simplex.hpp')==receipt['simplex_sha256']
 for n,pin in receipt['exact_sources'].items():assert fp.digest(model/n)==pin
 exe=proposal/'discover_robust'
 def robust_chunk(job,work,seconds):
  d=Path(job['directory']);stamp=str(time.time_ns());job['rounds']+=1
  if fp.digest(model/'model.json')!=job['model_sha256']:raise ValueError('Worker model binding changed')
  with (d/(stamp+'_DISCOVERY.log')).open('w') as log:
   subprocess.run([str(exe),str(d/'checkpoint.tree'),str(d/'next.tree'),str(seconds),'1000000',job['focus']],stdout=log,stderr=subprocess.STDOUT,check=True)
  info=fp.run_verify(model/'verify',d/'next.tree');inside=info['open']-len(job['steps'])
  if inside<0:raise ValueError('Worker erased an unpaid ancestor sibling')
  with open(os.devnull,'wb') as sink:fp.copy_focused_payload(d/'next.tree',job['steps'],sink)
  info.update(target_open=inside,model_sha256=job['model_sha256'],tree_sha256=fp.digest(d/'next.tree'),search_seconds=seconds,
              focus=job['focus'],rounds=job['rounds'],scope='ONE_FRONTIER_ONLY_NO_WHOLE_ROOT_CREDIT',proposal='validated_long_double_v1')
  fp.write_json(d/(stamp+'_ACCEPTANCE.json'),info);os.replace(d/'next.tree',d/'checkpoint.tree');fp.write_json(d/'STATUS.json',info)
  return info
 fp.job_chunk=robust_chunk
 current=out/'CURRENT_STATE.json'
 if current.exists():accepted=json.loads(current.read_text())['models']
 else:accepted={a.model:json.loads((root/'parallel/CURRENT_STATE.json').read_text())['models'][a.model]}
 info=accepted[a.model]
 assert fp.digest(info['tree'])==info['tree_sha256'] and info['model_sha256']==fp.PINS[a.model]
 inputs={a.model:Path(info['tree'])} if info['open'] else {}
 deadline=time.monotonic()+a.seconds;index=len(list(out.glob('wave_*')))
 while inputs and time.monotonic()<deadline:
  index+=1;wave=out/f'wave_{index:03d}';jobs,manifest=fp.prepare_wave(work,wave,inputs,max(80,2*a.workers))
  print(json.dumps({'event':'robust_wave_prepared','wave':index,'frontiers':len(jobs),'workers':a.workers}),flush=True)
  fp.execute_wave(work,wave,jobs,a.workers,min(deadline,time.monotonic()+a.wave_seconds),a.chunk)
  results=fp.graft_wave(work,wave,jobs,manifest);accepted.update(results)
  fp.write_json(current,{'status':'ORIGINAL_MODEL_ROOT_COMPLETE' if accepted[a.model]['open']==0 else 'EXACT_PARTIAL_ORIGINAL_ROOT',
    'models':accepted,'last_wave':index,'workers_cap':a.workers,'discovery_proposal':'validated_long_double_v1','whole_height_claim_requires_both_complete':True})
  print(json.dumps({'event':'original_root_accepted','wave':index,'model':a.model,
    **{k:accepted[a.model][k] for k in ('nodes','leaves','open','max_depth')}}),flush=True)
  inputs={a.model:Path(accepted[a.model]['tree'])} if accepted[a.model]['open'] else {}
  if (out/'STOP_AFTER_WAVE').exists():break
 print(json.dumps({'status':'MODEL_COMPLETE' if accepted[a.model]['open']==0 else 'SOFT_BUDGET_EXACT_CHECKPOINT_SAVED',
   'state':str(current),'whole_height_claim_requires_both_complete':True}),flush=True)

if __name__=='__main__':main()
