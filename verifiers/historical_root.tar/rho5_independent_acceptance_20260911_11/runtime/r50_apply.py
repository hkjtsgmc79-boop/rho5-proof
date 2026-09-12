#!/usr/bin/env python3
"""Apply only new strict certificates at bound actual OPEN indices/paths/boxes."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as Q
import argparse,gzip,json,os,time
from r50_protocol import *
def main():
    p=argparse.ArgumentParser();p.add_argument('--tree',type=Path,required=True);p.add_argument('--results',type=Path,nargs='+',required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
    a.out.mkdir();data=json.loads(a.tree.read_text());box=structure(data);desired={};start=time.monotonic()
    for directory in a.results:
        for path in sorted(directory.glob('result_*.json')):
            record=json.loads(path.read_text())
            if record['status']=='OPEN':continue
            if record['index']not in desired:desired[record['index']]=record
    stack=[(box,'')];kinds=Counter();delta=Counter();maximum=0;volume=Q(0);applied=[]
    with gzip.open(a.out/'OPEN_FRONTIERS.jsonl.gz','wt')as stream:
        for index,node in enumerate(data['nodes']):
            b,route=stack.pop();maximum=max(maximum,len(route))
            if node['kind']=='S':
                left,right=tp.halve(b,node['axis']);stack.extend([(right,route+'1'),(left,route+'0')])
            if index in desired:
                r=desired[index]
                assert node=={'kind':'O'}and r['path']==route and r['box']==[v.data()for v in b]and r['box_sha256']==gp.box_hash(b)
                # Discovery already exact-checked each proposal. This step only
                # stages it at its actual owner. The required final whole-root
                # replay checks every new terminal again, with parallel workers.
                status=r['status'];assert status in('EMPTY','SAFE');delta[status]+=1
                node=r['node'];data['nodes'][index]=node;applied.append({'index':index,'path':route,'box_sha256':r['box_sha256'],'kind':node['kind'],'status':status})
            if node['kind']=='O':
                volume+=Q(1,2**len(route));stream.write(json.dumps({'index':index,'path':route,'box':[v.data()for v in b]})+'\n')
            kinds[node['kind']]+=1
    assert not stack and len(applied)==len(desired)
    target=a.out/'B17_ROOT.json';target.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
    result={'status':'R50_CERTIFICATES_GRAFTED_FULL_ORIGINAL_ROOT_REPLAY_REQUIRED','parent_tree_sha256':sha(a.tree),'tree_sha256':sha(target),
            'nodes':len(data['nodes']),'kinds':dict(kinds),'open':kinds['O'],'max_depth':maximum,'new_outcomes':dict(delta),
            'applied':applied,'normalized_open_box_volume':str(volume),'source_result_directories':[str(p)for p in a.results],
            'binding':binding(),'seconds':time.monotonic()-start,'whole_B_closed':False,'macro_ledger':'14/15'}
    (a.out/'APPLY_RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='applied'},indent=2))
if __name__=='__main__':main()
