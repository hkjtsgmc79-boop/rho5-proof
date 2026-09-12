"""Bounded independent parent jobs; never graft or mutate a controller tree."""
from pathlib import Path
import os,json,time,argparse,multiprocessing
from concurrent.futures import ProcessPoolExecutor,as_completed
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'

def worker(job):
 from discover_branches import discover
 from discovery import atomic_json
 parent,out,seconds,nodes,depth,profile,waves=job
 path=Path(out)/f'p{parent["index"]}.json'
 try:
  r=discover(parent,path,seconds,nodes,depth,profile,waves)
 except Exception as e:
  r={'status':'ERROR','index':parent['index'],'error':repr(e),'counts':{'O':1},'whole_B_closed':False}
 atomic_json(Path(out)/f'p{parent["index"]}.result.json',r)
 return r

def main():
 p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True,help='JSON array of actual parent records, or a directory of p<index>.json records')
 p.add_argument('--output',type=Path,required=True);p.add_argument('--workers',type=int,default=4);p.add_argument('--seconds',type=float,default=120);p.add_argument('--nodes',type=int,default=511);p.add_argument('--depth',type=int,default=24);p.add_argument('--waves-per-node',type=int,default=0);p.add_argument('--profile',default='PIVOT_CYCLE');a=p.parse_args()
 if not 1<=a.workers<=40:raise ValueError('Use 1..40 workers')
 records=[json.loads(x.read_text())for x in sorted(a.input.glob('p[0-9]*.json'))]if a.input.is_dir()else json.loads(a.input.read_text())
 if not isinstance(records,list)or not records:raise ValueError('No supplied parent records')
 ids=[r['index']for r in records]
 if len(ids)!=len(set(ids)):raise ValueError('Duplicate parent jobs')
 a.output.mkdir(parents=True,exist_ok=True)
 (a.output/'JOB_PARAMETERS.json').write_text(json.dumps({'indices':ids,'workers':a.workers,'seconds':a.seconds,'nodes':a.nodes,'depth':a.depth,'waves_per_node':a.waves_per_node,'profile':a.profile},indent=2)+'\n')
 t=time.monotonic();results=[]
 with ProcessPoolExecutor(max_workers=a.workers,mp_context=multiprocessing.get_context('spawn')) as ex:
  fut=[ex.submit(worker,(r,str(a.output),a.seconds,a.nodes,a.depth,a.profile,a.waves_per_node))for r in records]
  for f in as_completed(fut):
   r=f.result();results.append(r);print(json.dumps({'index':r['index'],'status':r['status'],'counts':r.get('counts'),'seconds':r.get('including_final_replay_seconds'),'done':len(results)},ensure_ascii=False),flush=True)
 summary={'status':'V44_BOUNDED_PARENT_BATCH_FINISHED','evaluated':len(results),'complete_parent_ids':sorted(r['index']for r in results if r['status'] in ('EMPTY','SAFE')),'unpaid_parent_ids':sorted(r['index']for r in results if r['status'] not in ('EMPTY','SAFE')),'wall_seconds':time.monotonic()-t,'results':results,'whole_B_closed':False,'original_tree_modified':False}
 (a.output/'BATCH_RESULT.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({k:v for k,v in summary.items()if k!='results'},ensure_ascii=False),flush=True)
if __name__=='__main__':main()
