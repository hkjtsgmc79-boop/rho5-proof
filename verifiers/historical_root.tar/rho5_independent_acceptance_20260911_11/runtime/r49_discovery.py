#!/usr/bin/env python3
"""One bounded OPEN-frame pass, ordinary contraction first, optional graph fallback.
No continuous splits; all proposals strictly checked before any final insertion.
"""
from pathlib import Path
from collections import Counter
from concurrent.futures import ProcessPoolExecutor,as_completed
import argparse,gzip,hashlib,json,multiprocessing,os,random,sys,time
for key in('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[key]='1'
from r49_protocol import *
def worker(args):
    record,mode,full_graph,skip_ordinary=args
    if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
    start=time.monotonic();node=None if skip_ordinary else ordinary_propose(record['box']);ordinary_seconds=time.monotonic()-start;chart_counts=Counter();visited=0;cover=None
    if node is None and mode=='graph':
        import discover
        parent=gp.parent_enclosure(record['box']);children={label:{'kind':'O'}for label in gp.GRAPH_LABELS}
        for label in gp.GRAPH_LABELS:
            out=gp.contract_chart(parent,label)
            if out['status']=='EMPTY':child={'kind':'I'}
            elif gp.safe_port(out['aux_image'])is not None:child={'kind':'A'}
            else:child=discover.lp_propose(out['aux_image'],label)or{'kind':'O'}
            children[label]=child;visited+=1;chart_counts[child['kind']]+=1
            if child['kind']=='O'and not full_graph:break
        cover={'rule':gp.RULE,'rule_identity':gp.rule_identity(),'model_sha256':sha(gp.paths.FROZEN/'models/B17_FULL.json'),
               'box_sha256':gp.box_hash(record['box']),'children':children}
        if visited==189 and chart_counts['O']==0:node={'kind':'G','cover':cover}
    before=time.monotonic();status=verify_leaf(record['box'],node)if node else'OPEN';verify_seconds=time.monotonic()-before
    return {'index':record['index'],'path':record['path'],'depth':len(record['path']),'box':record['box'],'box_sha256':gp.box_hash(record['box']),
            'status':status,'node':node,'ordinary_seconds':ordinary_seconds,'seconds':time.monotonic()-start,'verification_seconds':verify_seconds,
            'charts_visited':visited,'chart_outcomes':dict(chart_counts),'partial_cover':cover if node is None else None}
def load_frontiers(path):
    with gzip.open(path,'rt')as f:return [json.loads(line)for line in f]
def main():
    p=argparse.ArgumentParser();p.add_argument('--frontiers',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--workers',type=int,default=40);p.add_argument('--samples',type=int,default=0);p.add_argument('--exclude-known',action='store_true');p.add_argument('--exclude-results',type=Path,nargs='+');p.add_argument('--mode',choices=('ordinary','graph'),default='ordinary');p.add_argument('--full-graph',action='store_true');p.add_argument('--ordinary-already-tried',action='store_true');a=p.parse_args()
    if not 1<=a.workers<=40:raise ValueError('40-worker cap')
    if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
    a.out.mkdir();records=load_frontiers(a.frontiers)
    if a.exclude_known:
        known={r['path']for r in json.loads((ROOT/'v39/inputs/diagnostics/audit_final/SAMPLE_CONTROLS.json').read_text())};records=[r for r in records if r['path']not in known]
    if a.exclude_results:
        excluded=set()
        for directory in a.exclude_results:
            for path in directory.glob('result_*.json'):
                r=json.loads(path.read_text())
                if r['status']!='OPEN':excluded.add(r['path'])
        records=[r for r in records if r['path']not in excluded]
    population=len(records)
    if a.samples:
        records=random.Random(490939).sample(records,min(a.samples,len(records)))
    write=lambda path,data:path.write_text(json.dumps(data,indent=2)+'\n')
    write(a.out/'INPUT.json',{'source_sha256':sha(a.frontiers),'population':population,'samples':len(records),'mode':a.mode,
                           'full_graph':a.full_graph,'skip_ordinary':a.ordinary_already_tried,'records':[{'index':r['index'],'path':r['path'],'box':r['box']}for r in records],'binding':binding()})
    start=time.monotonic();completed=[]
    with ProcessPoolExecutor(max_workers=a.workers,mp_context=multiprocessing.get_context('spawn'))as pool:
        futures=[pool.submit(worker,(record,a.mode,a.full_graph,a.ordinary_already_tried))for record in records]
        for f in as_completed(futures):
            r=f.result();write(a.out/f"result_{r['index']:07d}.json",r);completed.append({k:v for k,v in r.items()if k not in('box','node','partial_cover')})
            if len(completed)%40==0:print(json.dumps({'completed':len(completed),'total':len(records),'closed':sum(r['status']!='OPEN'for r in completed),'seconds':time.monotonic()-start}),flush=True)
    result={'status':'R49_FRONTIER_PASS_EXACT_PROPOSALS_COMPLETE','input_population':population,'evaluated':len(records),'workers':a.workers,
            'mode':a.mode,'full_graph':a.full_graph,'outcomes':dict(Counter(r['status']for r in completed)),
            'closed_by_wrapper':dict(Counter(json.loads((a.out/f"result_{r['index']:07d}.json").read_text())['node']['kind']for r in completed if r['status']!='OPEN')),
            'ordinary_cpu_seconds':sum(r['ordinary_seconds']for r in completed),'worker_cpu_wall_sum_seconds':sum(r['seconds']for r in completed),
            'wall_seconds':time.monotonic()-start,'charts_visited':sum(r['charts_visited']for r in completed),'binding':binding(),
            'whole_B_closed':False,'root_insertion_and_replay_still_required':True,'macro_ledger':'14/15'}
    write(a.out/'RESULT.json',result);print(json.dumps(result,indent=2))
if __name__=='__main__':main()
