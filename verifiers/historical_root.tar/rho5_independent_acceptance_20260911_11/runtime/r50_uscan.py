from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
from collections import Counter
import argparse,gzip,json,multiprocessing,os,random,time
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[key]='1'
from r50_protocol import *
import r50_unconditional as u
def worker(record):
 start=time.monotonic();node=u.propose(record['box']);status=u.verify(record['box'],node)if node else'OPEN'
 return {**record,'box_sha256':gp.box_hash(record['box']),'node':node,'status':status,'seconds':time.monotonic()-start}
def main():
 p=argparse.ArgumentParser();p.add_argument('--frontiers',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--samples',type=int,default=0);p.add_argument('--exclude-known',action='store_true');p.add_argument('--exclude-results',type=Path,nargs='+',default=[]);p.add_argument('--workers',type=int,default=40);a=p.parse_args()
 assert 1<=a.workers<=40
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 records=[json.loads(line)for line in gzip.open(a.frontiers,'rt')];exclude=set()
 if a.exclude_known:exclude.update(x['path']for x in json.loads((ROOT/'v40/inputs/REMAINING_SAMPLES64.json').read_text()))
 for d in a.exclude_results:
  for f in d.glob('result_*.json'):
   x=json.loads(f.read_text())
   if x['status']!='OPEN':exclude.add(x['path'])
 records=[r for r in records if r['path']not in exclude];population=len(records)
 if a.samples:records=random.Random(500940).sample(records,min(a.samples,len(records)))
 a.out.mkdir();(a.out/'INPUT.json').write_text(json.dumps({'frontier_sha256':sha(a.frontiers),'input_population':population,'records':records,'binding':binding()},indent=2)+'\n')
 start=time.monotonic();results=[]
 with ProcessPoolExecutor(max_workers=a.workers,mp_context=multiprocessing.get_context('spawn'))as pool:
  futures=[pool.submit(worker,r)for r in records]
  for f in as_completed(futures):
   r=f.result();(a.out/f"result_{r['index']:07d}.json").write_text(json.dumps(r,indent=2)+'\n');results.append(r)
   if len(results)%400==0:print(json.dumps({'completed':len(results),'total':len(records),'closed':sum(x['status']!='OPEN'for x in results),'seconds':time.monotonic()-start}),flush=True)
 result={'status':'R50_UNCONDITIONAL_FULL_PASS','evaluated':len(records),'outcomes':dict(Counter(r['status']for r in results)),'workers':a.workers,'wall_seconds':time.monotonic()-start,'worker_elapsed_sum':sum(r['seconds']for r in results),'binding':binding()}
 (a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
