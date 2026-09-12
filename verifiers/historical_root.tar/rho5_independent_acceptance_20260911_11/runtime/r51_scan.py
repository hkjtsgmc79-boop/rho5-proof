"""Bounded profile/wave passes. Every saved trajectory replays through original V41."""
from pathlib import Path
from collections import Counter
from concurrent.futures import ProcessPoolExecutor,as_completed
import argparse,gzip,json,multiprocessing,os,random,shutil,time
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
from r51_protocol import *
from discovery import discover_parent
def worker(args):
 item,directory,profile,waves,seconds,resume=args
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 start=time.monotonic();path=Path(directory)/f"certificate_{item['index']:07d}.json"
 if resume:shutil.copy2(resume,path)
 receipt=discover_parent(item['box'],path,profile,max_waves=waves,seconds=seconds)
 node=json.loads(path.read_text());status=receipt['status']
 assert status in ('EMPTY','SAFE','OPEN')
 result={**item,'box_sha256':gp.box_hash(item['box']),'status':status,'node':node if status!='OPEN'else None,
  'partial_certificate':node if status=='OPEN'else None,'receipt':receipt,'seconds':time.monotonic()-start,'profile':profile}
 (Path(directory)/f"result_{item['index']:07d}.json").write_text(json.dumps(result,indent=2)+'\n')
 return {'index':item['index'],'status':status,'profile':profile,'seconds':result['seconds'],'waves':receipt['waves'],'bounds':receipt['bounds'],'reason':receipt.get('discovery_reason','already_closed')}
def main():
 p=argparse.ArgumentParser();p.add_argument('--frontiers',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
 p.add_argument('--workers',type=int,default=40);p.add_argument('--samples',type=int,default=0);p.add_argument('--exclude-known',action='store_true')
 p.add_argument('--exclude-results',type=Path,nargs='+',default=[]);p.add_argument('--exclude-tested',type=Path,nargs='+',default=[]);p.add_argument('--resume-results',type=Path,nargs='+',default=[])
 p.add_argument('--profile',choices=('BASE','PIVOT','CYCLE','PIVOT_CYCLE'),default='BASE');p.add_argument('--max-waves',type=int,default=3);p.add_argument('--seconds',type=float,default=120);a=p.parse_args()
 assert 1<=a.workers<=40 and 0<=a.max_waves<=128 and a.seconds>=0
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 a.out.mkdir();records=[json.loads(s)for s in gzip.open(a.frontiers,'rt')];excluded=set();resumes={}
 if a.exclude_known:excluded.update(r['reported_original_index']for r in json.loads((ROOT/'v41/INSERTION_INDEX.json').read_text()))
 for directory in a.exclude_results+a.exclude_tested:
  for path in directory.glob('result_*.json'):
   r=json.loads(path.read_text())
   if directory in a.exclude_tested or r['status']!='OPEN':excluded.add(r['index'])
 for directory in a.resume_results:
  for path in directory.glob('result_*.json'):
   r=json.loads(path.read_text())
   if r['status']=='OPEN'and r['profile']==a.profile:resumes[r['index']]=str(directory/f"certificate_{r['index']:07d}.json")
 records=[r for r in records if r['index']not in excluded];population=len(records)
 if a.samples:records=random.Random(510941).sample(records,min(a.samples,len(records)))
 info={'input_population':population,'evaluated':len(records),'frontier_sha256':sha(a.frontiers),'profile':a.profile,'max_total_waves':a.max_waves,'soft_seconds_per_parent':a.seconds,'records':records,'binding':binding()}
 (a.out/'INPUT.json').write_text(json.dumps(info,indent=2)+'\n');start=time.monotonic();done=[]
 with ProcessPoolExecutor(max_workers=a.workers,mp_context=multiprocessing.get_context('spawn'))as pool:
  futures=[pool.submit(worker,(r,str(a.out),a.profile,a.max_waves,a.seconds,resumes.get(r['index'])))for r in records]
  for f in as_completed(futures):
   done.append(f.result())
   if len(done)%40==0:print(json.dumps({'completed':len(done),'total':len(records),'closed':sum(x['status']!='OPEN'for x in done),'seconds':time.monotonic()-start}),flush=True)
 result={'status':'R51_EXACT_TRACE_DISCOVERY_COMPLETE','input_population':population,'evaluated':len(records),'outcomes':dict(Counter(x['status']for x in done)),
  'closed_with_zero_dual_waves':sum(x['status']!='OPEN'and x['waves']==0 for x in done),'profile':a.profile,'max_total_waves':a.max_waves,'workers':a.workers,
  'worker_elapsed_sum':sum(x['seconds']for x in done),'wall_seconds':time.monotonic()-start,'waves':sum(x['waves']for x in done),'bound_certificates':sum(x['bounds']for x in done),
  'stop_reasons':dict(Counter(x['reason']for x in done)),'binding':binding(),'whole_B_closed':False,'macro_ledger':'14/15'}
 (a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
