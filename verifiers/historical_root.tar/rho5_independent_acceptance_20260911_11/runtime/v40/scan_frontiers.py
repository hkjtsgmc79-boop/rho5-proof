#!/usr/bin/env python3
"""Sidecar short-batch discovery on reported frontier boxes, not a root verifier."""
import os
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
from pathlib import Path
import gzip,json,argparse,concurrent.futures
from discover_parent import run

def worker(task):
 item,output,seconds,complete=task
 return run(item,output,seconds,complete)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('input');ap.add_argument('--output',required=True)
 ap.add_argument('--workers',type=int,default=4);ap.add_argument('--limit',type=int,default=160)
 ap.add_argument('--seconds-per-parent',type=float,default=120);ap.add_argument('--complete-scan',action='store_true')
 args=ap.parse_args()
 if args.workers<1 or args.limit<1 or args.seconds_per_parent<=0:raise ValueError('positive budgets required')
 p=Path(args.input);text=(gzip.open(p,'rt')if p.suffix=='.gz'else p.open()).read()
 try:data=json.loads(text);items=data if isinstance(data,list)else data.get('samples',[data])
 except json.JSONDecodeError:items=[json.loads(line)for line in text.splitlines()if line.strip()]
 items=items[:args.limit];out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
 from protocol import validate_box,box_hash
 tasks=[];keys=set()
 for i,item in enumerate(items):
  box=validate_box(item['box']);digest=box_hash(box)
  if digest in keys:raise ValueError('Duplicate actual box in this batch')
  keys.add(digest);item=dict(item);item['box']=box
  filename=f"frame_{item.get('index',i)}_{digest[:12]}.json"
  tasks.append((item,str(out/filename),args.seconds_per_parent,args.complete_scan))
 results=[]
 with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers)as pool:
  for result in pool.map(worker,tasks):
   results.append(result);print(json.dumps(result),flush=True)
   summary={'status':'SIDECAR_DIAGNOSTIC_NOT_ORIGINAL_ROOT_CLOSURE','receipts':results,
    'parents_closed':sum(r['children']['OPEN']==0 for r in results),'parents_tested':len(results),
    'original_tree_modified':False,'whole_B_closed':False,'macro_ledger':'14/15'}
   tmp=out/'BATCH_RESULTS.tmp';tmp.write_text(json.dumps(summary,indent=2)+'\n');os.replace(tmp,out/'BATCH_RESULTS.json')
if __name__=='__main__':main()
