"""Cost-layered discovery using unchanged V40 proposals and exact parent verifier."""
from pathlib import Path
from collections import Counter
from concurrent.futures import ProcessPoolExecutor,as_completed
import argparse,gzip,json,multiprocessing,os,random,shutil,time
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[key]='1'
from r50_protocol import *
import discover_parent as dp
def worker(args):
 item,directory,modes,seconds,resume=args
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 start=time.monotonic();path=Path(directory)/f"cover_{item['index']:07d}.json"
 if resume:shutil.copy2(resume,path)
 original=dp.candidate
 try:
  dp.candidate=lambda parent,label,mode:original(parent,label,mode)if mode in modes else None
  receipt=dp.run(item,path,seconds=seconds,complete_scan=False)
 finally:dp.candidate=original
 cert=json.loads(path.read_text());counts=receipt['children'];status='OPEN'if counts['OPEN']else'SAFE'if counts['SAFE']else'EMPTY'
 result={'index':item['index'],'path':item['path'],'box':item['box'],'box_sha256':gp.box_hash(item['box']),
  'status':status,'node':{'kind':'W40','certificate':cert}if status!='OPEN'else None,
  'partial_cover':cert if status=='OPEN'else None,'receipt':receipt,'seconds':time.monotonic()-start}
 (Path(directory)/f"result_{item['index']:07d}.json").write_text(json.dumps(result,indent=2)+'\n')
 return {'index':item['index'],'status':status,'seconds':result['seconds'],'children':counts,'modes':receipt['modes']}
def main():
 p=argparse.ArgumentParser();p.add_argument('--frontiers',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
 p.add_argument('--workers',type=int,default=40);p.add_argument('--samples',type=int,default=0);p.add_argument('--exclude-known',action='store_true')
 p.add_argument('--exclude-results',type=Path,nargs='+',default=[]);p.add_argument('--resume-results',type=Path,nargs='+',default=[])
 p.add_argument('--modes',nargs='+',default=['FULL']);p.add_argument('--seconds',type=float,default=120);a=p.parse_args()
 assert 1<=a.workers<=40 and a.seconds>0 and set(a.modes)<={'FULL','QUOTIENT','PROJECTED','HOMOGENEOUS'}
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 a.out.mkdir();records=[json.loads(line)for line in gzip.open(a.frontiers,'rt')];excluded=set();resumes={}
 if a.exclude_known:excluded.update(r['path']for r in json.loads((ROOT/'v40/inputs/REMAINING_SAMPLES64.json').read_text()))
 for directory in a.exclude_results:
  for f in directory.glob('result_*.json'):
   r=json.loads(f.read_text())
   if r['status']!='OPEN':excluded.add(r['path'])
 for directory in a.resume_results:
  for f in directory.glob('result_*.json'):
   r=json.loads(f.read_text())
   if r['status']=='OPEN':resumes[r['index']]=str(directory/f"cover_{r['index']:07d}.json")
 records=[r for r in records if r['path']not in excluded];population=len(records)
 if a.samples:records=random.Random(500940).sample(records,min(a.samples,len(records)))
 info={'frontier_sha256':sha(a.frontiers),'input_population':population,'evaluated':len(records),'modes':a.modes,'soft_seconds_per_parent':a.seconds,'records':records,'binding':binding()}
 (a.out/'INPUT.json').write_text(json.dumps(info,indent=2)+'\n')
 started=time.monotonic();done=[]
 with ProcessPoolExecutor(max_workers=a.workers,mp_context=multiprocessing.get_context('spawn'))as pool:
  futures=[pool.submit(worker,(r,str(a.out),a.modes,a.seconds,resumes.get(r['index'])))for r in records]
  for f in as_completed(futures):
   done.append(f.result())
   if len(done)%40==0:print(json.dumps({'completed':len(done),'total':len(records),'closed':sum(x['status']!='OPEN'for x in done),'seconds':time.monotonic()-started}),flush=True)
 result={'status':'R50_EXACT_CHECKED_DISCOVERY_PASS','input_population':population,'evaluated':len(records),'outcomes':dict(Counter(x['status']for x in done)),
  'worker_elapsed_sum':sum(x['seconds']for x in done),'wall_seconds':time.monotonic()-started,'workers':a.workers,'modes':a.modes,
  'binding':binding(),'whole_B_closed':False,'macro_ledger':'14/15'}
 (a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
