#!/usr/bin/env python3
"""Fresh original-root traversal; all terminal leaves independently checked once.
Worker parallelism changes only leaf evaluation order, never root/box ownership.
"""
from pathlib import Path
from collections import Counter
from concurrent.futures import ProcessPoolExecutor,wait,FIRST_COMPLETED
import argparse,hashlib,json,multiprocessing,os,time
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[key]='1'
import tree_protocol as tp
from r49_protocol import structure,binding,verify_leaf
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check_chunk(payload):
    backend,items=payload
    counts=Counter()
    for box,node in items:
        status=verify_leaf(box,node,backend)
        if status not in ('EMPTY','SAFE'):raise ValueError('unaccepted leaf')
        counts[status]+=1;counts['checked']+=1
        counts['enclosure:'+('V39_'+node['kind']if node['kind']in('G','V')else node.get('enclosure','original_v37'))]+=1
        counts['kind:'+node['kind']]+=1
    return dict(counts)
def replay(tree,workers=40,backend='native',allow_open=False):
    start=time.monotonic();tree=Path(tree);tree_hash=sha(tree)
    manifest=json.loads((ROOT/'R49_SOURCE_MANIFEST.json').read_text())
    for name,digest in manifest['files'].items():assert sha(ROOT/name)==digest,name
    tp.verify_partition();data=json.loads(tree.read_text());box=structure(data)
    stack=[(box,0)];counts=Counter();maximum=0;terminals=Counter();batch=[];futures=set()
    def collect(done):
        for future in done:terminals.update(future.result())
    with ProcessPoolExecutor(max_workers=workers,mp_context=multiprocessing.get_context('spawn'))as pool:
        for node in data['nodes']:
            if not stack:raise ValueError('unvisited records')
            box,depth=stack.pop();maximum=max(maximum,depth);counts[node['kind']]+=1
            if node['kind']=='S':
                left,right=tp.halve(box,node['axis']);stack.extend([(right,depth+1),(left,depth+1)])
            elif node['kind']=='O':pass
            else:batch.append((box,node))
            if len(batch)>=128:
                futures.add(pool.submit(check_chunk,(backend,batch)));batch=[]
                if len(futures)>=2*workers:
                    done,futures=wait(futures,return_when=FIRST_COMPLETED);collect(done)
        if batch:futures.add(pool.submit(check_chunk,(backend,batch)))
        while futures:
            done,futures=wait(futures,return_when=FIRST_COMPLETED);collect(done)
    if stack:raise ValueError('truncated tree')
    assert terminals['checked']==counts['E']+counts['C']+counts['H']+counts['V']+counts['G']
    assert len(data['nodes'])==2*counts['S']+1
    assert terminals['EMPTY']+terminals['SAFE']+counts['O']==counts['S']+1
    assert sha(tree)==tree_hash,'tree changed during replay'
    if counts['O'] and not allow_open:raise ValueError(f"{counts['O']} unpaid frontiers")
    result={'status':'COMPLETE_ALPHA_COVERAGE'if not counts['O']else'PARTIAL_EXACT_COVERAGE_ONLY',
            'nodes':len(data['nodes']),'splits':counts['S'],'contradictions':terminals['EMPTY'],'alpha_safe':terminals['SAFE'],
            'open':counts['O'],'max_depth':maximum,'kinds':dict(counts),'terminal_audit':dict(terminals),
            'whole_B_closed':not counts['O'],'macro_ledger':'14/15','controller_only_may_book_completion':True,
            'tree_sha256':tree_hash,'model_sha256':data['model_sha256'],'source_manifest_sha256':sha(ROOT/'R49_SOURCE_MANIFEST.json'),
            'r49_binding':binding(),'backend':backend,'workers':workers,'seconds':time.monotonic()-start,
            'scope':'Fresh traversal of actual original B17 root; every C/H/E terminal checked on its actual dyadic box; all original siblings retained',
            'old_leaf_backend':backend,'new_leaf_backend':'V39 original Fraction reference and versioned ordinary adapter'}
    return result
def main():
    p=argparse.ArgumentParser();p.add_argument('--tree',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--workers',type=int,default=40);p.add_argument('--backend',choices=('native','fraction'),default='native');p.add_argument('--allow-open',action='store_true');a=p.parse_args()
    if not 1<=a.workers<=40:raise ValueError('40-worker cap')
    if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
    if a.out.exists():raise ValueError('immutable receipt already exists')
    result=replay(a.tree,a.workers,a.backend,a.allow_open);a.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
