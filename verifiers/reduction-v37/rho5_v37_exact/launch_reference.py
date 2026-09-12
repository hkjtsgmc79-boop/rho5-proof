#!/usr/bin/env python3
"""Short-budget CPU diagnostic for the 40 exact B17 tiles.
Not claimed faster than the user's existing compiled search backend.
One process per tile; no nested BLAS threads. Reuse output directory to resume.
"""
import os
for k in ('OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[k]='1'
import json, argparse, multiprocessing
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed

def worker(args):
    task,seconds,nodes,path=args
    from probe import run
    try:return {'task':task,'result':run(task,seconds,nodes,path)}
    except Exception as e:return {'task':task,'status':'ERROR_PREVIOUS_ACCEPTED_FILE_PRESERVED','error':str(e)}

def launch(tasks,workers,seconds,nodes,directory):
    from tree_protocol import verify_partition
    verify_partition();d=Path(directory);d.mkdir(parents=True,exist_ok=True)
    args=[(i,seconds,nodes,str(d/f'task_{i:02d}.json'))for i in tasks]
    receipts=[]
    with ProcessPoolExecutor(max_workers=workers,mp_context=multiprocessing.get_context('spawn'))as ex:
        fs=[ex.submit(worker,x)for x in args]
        for f in as_completed(fs):
            out=f.result();receipts.append(out);print(json.dumps(out),flush=True)
            (d/'DIAGNOSTIC_RECEIPTS.json').write_text(json.dumps(sorted(receipts,key=lambda v:v['task']),indent=2)+'\n')
    return receipts
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--workers',type=int,default=2);p.add_argument('--seconds',type=float,default=30);p.add_argument('--nodes',type=int,default=64);p.add_argument('--tasks',type=int,nargs='*',default=list(range(40)));p.add_argument('--output',default='reference_campaign');a=p.parse_args()
    if a.workers<1 or a.workers>40 or a.nodes<1 or a.seconds<=0:raise SystemExit('Invalid diagnostic budget')
    launch(a.tasks,a.workers,a.seconds,a.nodes,a.output)
