"""Exact rebasing diagnostic, NOT a parent certificate and NOT a C42 wrapper.

Replays two received old/current unconditional prefixes and the four specifically
OPEN conditional traces. Reuses old integer weights only as candidate vectors;
every inequality, residual and new endpoint is recalculated on its actual box.
No claim is made about the 187 other children or the unreceived root tree.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse, hashlib, json, sys, time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'dependency/v41'))
import v41_protocol as vp
import dual_box as db
import source_access as sa

def digest(obj):return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def exact_endpoint(box,node):
    expected={'kind',*vp.bind(box),'trace'}
    if not isinstance(node,dict) or node.get('kind')!='U41' or set(node)!=expected:raise ValueError('U41 source required')
    for k,v in vp.bind(box).items():
        if node.get(k)!=v:raise ValueError('Unconditional prefix identity '+k)
    return db.replay_trace(box,node['trace'],cross_check=True,allow_open=True)
def child(aux,trace,label):
    if label not in sa.fs.GRAPH_LABELS:raise ValueError('Unknown conditional label')
    if set(trace)!={'profile','waves','terminal'} or trace['terminal']!={'kind':'O'}:raise ValueError('Only the received OPEN traces')
    profile=trace['profile'];db.validate_profile(profile)
    out=db.common_contract({'status':'BOUNDED','aux_image':aux},label,profile)
    used=[]
    for wave in trace['waves']:
        if out['status']=='EMPTY':break
        out=db.apply_wave(out,wave,label,profile,True);used.append(wave)
    return out,used

def certified_meet(a,b,label,profile):
    if a['status']=='EMPTY' or b['status']=='EMPTY':return {'status':'EMPTY'}
    box=[]
    for x,y in zip(a['aux_image'],b['aux_image']):
        lo=max(Q(x[0]),Q(y[0]));hi=min(Q(x[1]),Q(y[1]))
        if lo>hi:return {'status':'EMPTY','reason':'intersection of separately verified same-source enclosures'}
        box.append([str(lo),str(hi)])
    return db.common_contract({'status':'BOUNDED','aux_image':box},label,profile)

def compare_aux(old,new):
    if old['status']=='EMPTY' or new['status']=='EMPTY':return dict(old_status=old['status'],new_status=new['status'])
    a=old['aux_image'];b=new['aux_image']
    aw=[Q(u)-Q(l)for l,u in a];bw=[Q(u)-Q(l)for l,u in b]
    return dict(old_status=old['status'],new_status=new['status'],old_endpoint_sha256=digest(a),new_endpoint_sha256=digest(b),
      old_width_sum=str(sum(aw)),new_width_sum=str(sum(bw)),width_sum_ratio=str(sum(bw)/sum(aw)),
      old_F_upper=a[23][1],new_F_upper=b[23][1],
      coordinate_widths=[dict(i=i,old=str(x),new=str(y))for i,(x,y)in enumerate(zip(aw,bw))])

def run(index=None,output=None):
    started=time.monotonic(); records=[]
    ids=[index]if index is not None else[491229,674450]
    for idx in ids:
        obj=json.loads((ROOT/f'controls/round52/{idx}.json').read_text())
        old=exact_endpoint(obj['box'],obj['C42_prefix']);new=exact_endpoint(obj['box'],obj['partial_certificate'])
        children=[]
        print('Verified unconditional prefixes',idx,'old/current waves',old['waves'],new['waves'],flush=True)
        for label,trace in obj['open_children'].items():
            oo,uw=child(old['aux_image'],trace,label);nn,nw=child(new['aux_image'],trace,label)
            comp=compare_aux(oo,nn)
            meet=certified_meet(oo,nn,label,trace['profile'])
            children.append(dict(label=label,old_waves=len(uw),new_waves=len(nw),rechecked_new_bounds=sum(map(len,nw)),comparison=comp,new_endpoint=nn.get('aux_image'),meet_endpoint=meet.get('aux_image'),meet_status=meet['status'],old_to_meet=compare_aux(oo,meet),profile=trace['profile'],
              old_conditional_inside_current_unconditional=all(Q(a[0])>=Q(b[0]) and Q(a[1])<=Q(b[1])for a,b in zip(oo['aux_image'],new['aux_image'])),
              meet_equals_old=meet.get('aux_image')==oo.get('aux_image')))
            print('Rechecked conditional',idx,label,oo['status'],nn['status'],flush=True)
        records.append(dict(index=idx,path=obj['path'],box_sha256=sa.fs.box_hash(obj['box']),old_prefix_sha256=digest(obj['C42_prefix']),current_prefix_sha256=digest(obj['partial_certificate']),
          old_prefix_waves=old['waves'],current_prefix_waves=new['waves'],unconditional=compare_aux(old,new),children=children))
    result=dict(status='V43_R52_FOUR_GRAPH_REBASE_DIAGNOSTIC_CHECKED_NOT_PARENT_COVERAGE',records=records,
      full_189_graph_covers_replayed=False,unreceived_root_tree_replayed=False,new_parent_certificates=0,seconds=time.monotonic()-started)
    if output:Path(output).write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    return result
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--index',type=int,choices=[491229,674450]);ap.add_argument('--output');args=ap.parse_args()
    print(json.dumps(run(args.index,args.output),ensure_ascii=False))
