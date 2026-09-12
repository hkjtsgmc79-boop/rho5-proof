#!/usr/bin/env python3
"""Verify original paths/axes/boxes, graft exactly ten V39 covers, retain all siblings."""
from pathlib import Path
from collections import Counter
import copy,gzip,json,os,time
from r49_protocol import *
def main():
    if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
    out=ROOT/'graft10';out.mkdir();source=ROOT/'inherited/B17_COMPOSED_ROOT.json';data=json.loads(source.read_text());root=structure(data)
    assert sha(source)=='5dc6e39341e8cab78073d88a317f09a7c637b0da7c9ad53fe30da64c0846e9d4'
    samples=json.loads((ROOT/'v39/inputs/diagnostics/audit_final/SAMPLE_CONTROLS.json').read_text())
    wanted={samples[i]['path']:samples[i]for i in(0,22,28,34,39,48,50,52,57,58)}
    stack=[(root,'')];grafted=[];counts=Counter();start=time.monotonic();maximum=0
    with gzip.open(out/'OPEN_FRONTIERS.jsonl.gz','wt')as f:
        for index,node in enumerate(data['nodes']):
            box,path=stack.pop();maximum=max(maximum,len(path))
            if node['kind']=='S':
                left,right=tp.halve(box,node['axis']);stack.extend([(right,path+'1'),(left,path+'0')])
            if path in wanted:
                item=wanted[path];assert node=={'kind':'O'}and item['box']==[v.data()for v in box]
                certificate=json.loads((ROOT/'v39'/f"evidence/frontier_covers/sample_{item['sample']:02d}.json").read_text())
                replacement={'kind':'G','cover':certificate};assert verify_leaf(box,replacement)=='EMPTY'
                data['nodes'][index]=replacement;node=replacement
                grafted.append({'sample':item['sample'],'path':path,'index':index,'box_sha256':gp.box_hash(box),'cover_sha256':sha(ROOT/'v39'/f"evidence/frontier_covers/sample_{item['sample']:02d}.json")})
            if node['kind']=='O':f.write(json.dumps({'index':index,'path':path,'box':[v.data()for v in box]})+'\n')
            counts[node['kind']]+=1
    assert not stack and len(grafted)==10 and counts['O']==17645
    tree=out/'B17_ROOT.json';tree.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
    bad=0
    def reject(fn):
        nonlocal bad
        try:fn()
        except (ValueError,TypeError,KeyError,IndexError,AssertionError):bad+=1
        else:raise AssertionError('negative adapter control accepted')
    # These V proposals were supplied by the independently replayed ablation.
    v_checked=0
    for r in json.loads((ROOT/'v39/evidence/ablation.json').read_text())['records']:
        if r['kind']=='UNRESOLVED':continue
        box=samples[r['sample']]['box'];node=ordinary_wrap(box,{'kind':'I'}if r['kind']=='INTERVAL'else r['certificate'])
        assert verify_leaf(box,node)=='EMPTY';v_checked+=1
        wrong=copy.deepcopy(node);wrong['box_sha256']='0'*64;reject(lambda:verify_leaf(box,wrong))
        wrong=copy.deepcopy(node);wrong['rule_identity']='0'*64;reject(lambda:verify_leaf(box,wrong))
    box=samples[0]['box'];node={'kind':'G','cover':json.loads((ROOT/'v39/evidence/frontier_covers/sample_00.json').read_text())}
    badg=copy.deepcopy(node);badg['cover']['children'].pop(gp.GRAPH_LABELS[-1]);reject(lambda:verify_leaf(box,badg))
    badg=copy.deepcopy(node);badg['cover']['children'][gp.GRAPH_LABELS[0]]={'kind':'O'};reject(lambda:verify_leaf(box,badg))
    badg=copy.deepcopy(node);badg['cover']['box_sha256']='0'*64;reject(lambda:verify_leaf(box,badg))
    for mutation in(lambda d:d.update(task=0),lambda d:d.update(root_path='1'),lambda d:d.update(nodes=d['nodes'][:-1])):
        badtree=copy.deepcopy(data);mutation(badtree);reject(lambda:structure(badtree))
    result={'status':'TEN_G_COVERS_STRICTLY_VERIFIED_AND_GRAFTED_AT_ACTUAL_ORIGINAL_PATHS','parent_tree_sha256':sha(source),
            'tree_sha256':sha(tree),'nodes':len(data['nodes']),'kinds':dict(counts),'open':counts['O'],'max_depth':maximum,
            'new_contradictions':10,'grafted':grafted,'ordinary_adapter_positive_checks':v_checked,'adapter_bad_controls_rejected':bad,
            'binding':binding(),'seconds':time.monotonic()-start,'root_replay_still_required':True,'whole_B_closed':False,'macro_ledger':'14/15'}
    (out/'GRAFT_RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
