#!/usr/bin/env python3
"""Exact whole-frame ports, leaf-rule arithmetic, and corruption rejection.
These checks do not claim to complete the full B root.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,copy
from capacity import extract_frame,encode
from interval_capacity import I,oracle,root_box,ALPHA,GAMMA
from relaxation import margin,verify_leaf,LABELS,rows_and_bounds,N,FI
from tree_protocol import verify_tree,empty_tree,halve,verify_partition
ROOT=Path(__file__).parent

def independent_margin(aux,record):
    rows,boxes=rows_and_bounds(aux)
    # Separately form weighted dense rows and evaluate every remaining coefficient.
    combined=[sum(Q(w)*a.get(j,Q(0))for i,w in record['weights']for a,b in [rows[i]])for j in range(N)]
    rhs=sum(Q(w)*rows[i][1]for i,w in record['weights'])
    target=record.get('objective_weight',0)
    if record['kind']=='H':combined[FI]-=target
    value=rhs
    for c,box in zip(combined,boxes):
        value-=c*(box.lo if c>=0 else box.hi)
    if record['kind']=='H':value-=Q(target)*ALPHA
    return value

def main():
    records=json.loads((ROOT/'evidence/capacity_controls.json').read_text())
    ports=[];image=0;hs=[]
    for i in (0,4,8,12):
        rec=records[i];frame=extract_frame(rec['source_gap']);eps=Q(1,100000)
        box=[I(x-eps,x+eps).intersection(b)for x,b in zip(frame,root_box())]
        if not all(box):raise AssertionError('source outside root')
        o=oracle(box)
        assert o['status']=='SAFE'and o['port'].startswith('canonical_flow')
        exact=list(map(Q,rec['maximum']['point_gap']))
        for value,(l,h)in zip(exact,o['gap_image']):assert Q(l)<=value<=Q(h);image+=1
        ports.append({'source_control_case':rec['case'],'frame_radius':str(eps),'frame_box':[v.data()for v in box],
                      'status':'ALL_COMPLETE_SIX_VARIABLE_FIBRES_ALPHA_SAFE','certificate':o})
        # A genuine H arithmetic control at a zero-width frame. A tight source
        # row plus the exact F image makes an H certificate; this is a control,
        # not a newly claimed large height region.
        point=[I(x)for x in frame];p=oracle(point);assert p['status']=='SAFE'
        found=None
        for j in range(len(LABELS)):
            h={'kind':'H','weights':[[j,1]],'objective_weight':1}
            if margin(p['aux_image'],h)<=0:
                assert verify_leaf(point,h)=='SAFE';found=h;break
        assert found
        assert margin(p['aux_image'],found)==independent_margin(p['aux_image'],found)
        hs.append({'frame_box':[v.data()for v in point],'record':found,'margin':str(margin(p['aux_image'],found))})
    (ROOT/'evidence/frame_alpha_ports.json').write_text(json.dumps(ports,indent=2)+'\n')
    (ROOT/'evidence/H_arithmetic_controls.json').write_text(json.dumps(hs,indent=2)+'\n')
    # Replay all C leaves from the actual reference original-root checkpoint.
    tree=json.loads((ROOT/'evidence/reference_checkpoint.json').read_text());stack=[root_box()];cm=0
    for node in tree['nodes']:
        box=stack.pop()
        if node['kind']=='S':
            L,R=halve(box,node['axis']);stack.extend([R,L])
        elif node['kind']=='C':
            aux=oracle(box)['aux_image'];assert margin(aux,node)==independent_margin(aux,node)<0;cm+=1
    assert not stack
    original_result=verify_tree(tree,allow_open=True)
    assert original_result['open']>0
    # Independent raw rule arithmetic on all four H controls and actual C leaves.
    bad=0
    def reject(fn):
        nonlocal bad
        try:fn()
        except (ValueError,TypeError,KeyError,AssertionError,ZeroDivisionError):bad+=1
        else:raise AssertionError('corrupted input accepted')
    reject(lambda:verify_tree(tree))
    for mutation in (
       lambda d:d.update(model_sha256='0'*64),
       lambda d:d.update(root_path='1'),
       lambda d:d.update(nodes=d['nodes'][:-1]),
       lambda d:d.update(nodes=d['nodes']+[{'kind':'O'}]),
       lambda d:d.update(nodes=[{'kind':'E'}]),
       lambda d:d.update(nodes=[{'kind':'Q'}]),
       lambda d:d.update(nodes=[{'kind':'S','axis':17},{'kind':'O'},{'kind':'O'}]),
       lambda d:d.update(nodes=[{'kind':'S','axis':True},{'kind':'O'},{'kind':'O'}]),
    ):
        data=copy.deepcopy(tree);mutation(data);reject(lambda data=data:verify_tree(data,allow_open=True))
    box=[I(*v)for v in hs[0]['frame_box']];good=hs[0]['record'];row=good['weights'][0][0]
    for item in (
        {'kind':'H','weights':[[row,-1]],'objective_weight':1},
        {'kind':'H','weights':[[row,0]],'objective_weight':1},
        {'kind':'H','weights':[[row,True]],'objective_weight':1},
        {'kind':'H','weights':[[row,1],[row,1]],'objective_weight':1},
        {'kind':'H','weights':[[99999,1]],'objective_weight':1},
        {'kind':'H','weights':[[row,1]],'objective_weight':0},
        {'kind':'H','weights':[[row,1]],'objective_weight':True},
        {'kind':'C','weights':[]},
    ):reject(lambda item=item:verify_leaf(box,item))
    # Safely positive source control cannot be asserted to be a contradiction.
    reject(lambda:verify_leaf(box,{'kind':'C','weights':[[row,1]]}))
    result={'status':'V37_CANONICAL_FRAME_PORTS_AND_LEAF_RULES_PASS',
        'frame_safe_boxes':len(ports),'canonical_image_containment_checks':image,'H_arithmetic_controls':len(hs),
        'C_arithmetic_crosschecks':cm,'bad_inputs_rejected':bad,'partition':verify_partition(),'reference_root':original_result,
        'whole_B_closed':False,'ledger':'14/15'}
    (ROOT/'evidence/ports_result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
