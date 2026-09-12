"""Read-only scan of supplied B17 frontiers. Never grafts or mutates an old tree.
Supports JSON lists, JSON with a frontiers/samples/items array, and JSONL[.gz].
"""
import os
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
from pathlib import Path
import json,gzip,argparse,time
from concurrent.futures import ProcessPoolExecutor,as_completed
from discovery import discover_parent,atomic_json
from source_access import fs
from v41_protocol import bind

def load(path):
    path=Path(path);op=gzip.open if path.suffix=='.gz'else open
    with op(path,'rt',encoding='utf-8')as f:text=f.read()
    try:data=json.loads(text)
    except json.JSONDecodeError:data=[json.loads(line)for line in text.splitlines()if line.strip()]
    if isinstance(data,dict):
        for key in('frontiers','samples','items'):
            if key in data:data=data[key];break
    if not isinstance(data,list):raise ValueError('Expected an explicit list of B17 boxes')
    return data

def work(job):
    ordinal,item,ns=job
    box=item['box'];identity=bind(box);digest=identity['box_sha256']
    dst=Path(ns['output'])/(f'box_{digest[:24]}_{ns["profile"]}.json')
    try:
        result=discover_parent(box,dst,ns['profile'],ns['max_waves'],ns['seconds_per_parent'])
        return dict(ordinal=ordinal,reported_index=item.get('index'),reported_path=item.get('path'),box_sha256=digest,certificate=str(dst),result=result)
    except Exception as exc:
        return dict(ordinal=ordinal,reported_index=item.get('index'),box_sha256=digest,status='ERROR_NOT_CLOSED',error=str(exc))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input');ap.add_argument('--output',required=True)
    ap.add_argument('--workers',type=int,default=2);ap.add_argument('--limit',type=int,default=160)
    ap.add_argument('--seconds-per-parent',type=float,default=120);ap.add_argument('--max-waves',type=int,default=3)
    ap.add_argument('--profile',choices=('BASE','PIVOT','CYCLE','PIVOT_CYCLE'),default='BASE')
    args=ap.parse_args()
    if args.workers<1 or args.limit<1:ap.error('positive workers/limit required')
    items=load(args.input)[:args.limit];ns=vars(args);out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
    jobs=[(i,item,ns)for i,item in enumerate(items)];results=[];start=time.monotonic()
    # Limits are per-parent soft discovery budgets. Workers are independent;
    # termination can lose only a not-yet-accepted batch, never its old checkpoint.
    with ProcessPoolExecutor(max_workers=args.workers)as ex:
        for future in as_completed([ex.submit(work,job)for job in jobs]):
            r=future.result();results.append(r)
            atomic_json(out/'SCAN_RESULTS.json',dict(results=sorted(results,key=lambda x:x['ordinal']),seconds=time.monotonic()-start,original_tree_modified=False))
            print(r['ordinal'],r.get('result',{}).get('status',r.get('status')),flush=True)
    return dict(parents=len(results),certified=sum(r.get('result',{}).get('status')in('EMPTY','SAFE')for r in results),
       unfinished=sum(r.get('result',{}).get('status')not in('EMPTY','SAFE')for r in results),original_tree_modified=False,seconds=time.monotonic()-start)
if __name__=='__main__':print(json.dumps(main(),indent=2))
