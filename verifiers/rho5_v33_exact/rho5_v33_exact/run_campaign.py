#!/usr/bin/env python3
"""Offline continuation of frozen low-r models. Time budget is NOT a proof.
Example: python run_campaign.py --seconds 7200 --jobs 2 --chunk 120
The unchanged model hash is checked before each checkpoint is consumed.
"""
from pathlib import Path
import argparse,concurrent.futures,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parent

def task(name,args):
    path=ROOT/'models'/name;log=ROOT/'logs'/(name+'_offline_'+str(time.time_ns())+'.log')
    with log.open('w') as f:
        ret=subprocess.run([sys.executable,str(ROOT/'run_chunks.py'),str(path),'--seconds',str(args.seconds),'--chunk',str(args.chunk)],stdout=f,stderr=subprocess.STDOUT)
    result={'model':name,'exit_code':ret.returncode,'log':str(log.relative_to(ROOT))}
    if (path/'checkpoint.status.json').exists():result['checkpoint']=json.loads((path/'checkpoint.status.json').read_text())
    return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=7200);ap.add_argument('--jobs',type=int,default=2);ap.add_argument('--chunk',type=float,default=120);ap.add_argument('--models',nargs='+',default=['I210_214','II210_214']);a=ap.parse_args()
    if a.seconds<=0 or a.chunk<=0 or not 1<=a.jobs<=8:ap.error('positive budget/chunk, 1..8 jobs required')
    (ROOT/'logs').mkdir(exist_ok=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        out=list(pool.map(lambda n:task(n,a),a.models))
    (ROOT/'offline_run_summary.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
    print('Only a zero-open, independently verified tree establishes a full model bound. No promise that this time budget finishes the search.')
if __name__=='__main__':main()
