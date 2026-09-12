"""V42 wrappers over an unchanged, fully verified, unconditional U41 prefix.
B42 is an alpha-safe port (or high-empty B01 condition), NOT a C contradiction.
C42 covers ALL 189 prefix graphs at the SAME U41 endpoint. It is NOT old G41.
No cached enclosure or naked conditional weights are accepted as a root proof.
"""
from pathlib import Path
from functools import lru_cache
from fractions import Fraction as Q
import json,subprocess,sys
from _v42_bootstrap import ROOT,prepare,v41_api,centers,canonical_hash,sha
import transport_box as tb
RULE='V42_SAME_IMAGE_TRANSPORT_AND_CONDITIONAL_COVER_V1'
RULE_FILES=('_v42_bootstrap.py','transport_box.py','bound_protocol.py','verify_gain.py')
ROUND51_ROOT='dd56619d4e328241164d2aeb8ed71a5378494bef68838b01ace97120f0b7da58'

@lru_cache(None)
def require_gain():
    r=json.loads(subprocess.check_output([sys.executable,str(ROOT/'verify_gain.py')],text=True))
    if r['status']!='V42_ONE_SLACK_FOUR_CUBES_EXACT_PASS':raise ValueError('Gain certificate failed')
    if tuple(Q(x['cost'])for x in r['directions'])!=tb.ONE_SLACK_COSTS:raise ValueError('Gain identity')
    return r

def binding(box,prefix):
    vp,db,sa=v41_api();box=sa.inherited.validate_box(box)
    rule_id=canonical_hash({n:sha(ROOT/n)for n in RULE_FILES}|{'V41':vp.rule_identity(),
        'B02':sha(prepare()['b02']/'accepted_inputs/local_wall_certificate.json'),
        'alpha':sha(prepare()['b02']/'support/alpha.json') if (prepare()['b02']/'support/alpha.json').exists() else sha(sa.SOURCE/'dependency/alpha.json')})
    return dict(rule=RULE,rule_identity=rule_id,reported_round51_root_sha256=ROUND51_ROOT,box_sha256=sa.fs.box_hash(box),
                prefix_sha256=canonical_hash(prefix),model_sha256=sa.IDENTITY['b17_model_sha256'])

def endpoint(box,prefix,cross_check=True):
    """Same validation as the frozen U41 wrapper, retaining its verified image."""
    vp,db,sa=v41_api();box=sa.inherited.validate_box(box)
    expected={'kind',*vp.bind(box),'trace'}
    if not isinstance(prefix,dict)or prefix.get('kind')!='U41'or set(prefix)!=expected:
        raise ValueError('Requires complete unconditional U41 certificate, not an image')
    for k,v in vp.bind(box).items():
        if prefix.get(k)!=v:raise ValueError('Wrong U41 '+k)
    return db.replay_trace(box,prefix['trace'],allow_open=True,cross_check=cross_check)

def child_replay(aux,trace,label,cross_check=True,allow_open=False):
    _,db,sa=v41_api()
    if label not in sa.fs.GRAPH_LABELS:raise ValueError('Unknown graph')
    if not isinstance(trace,dict)or set(trace)!={'profile','waves','terminal'}:raise ValueError('Conditional trace schema')
    profile=trace['profile'];db.validate_profile(profile);waves=trace['waves']
    if not isinstance(waves,list)or len(waves)>128:raise ValueError('Conditional waves')
    out=db.common_contract({'status':'BOUNDED','aux_image':aux},label,profile)
    for wave in waves:out=db.apply_wave(out,wave,label,profile,cross_check)
    term=trace['terminal'];kind=term.get('kind')if isinstance(term,dict)else None
    result=dict(waves=len(waves),bounds=sum(map(len,waves)))
    if kind=='O':
        if term!={'kind':'O'}or not allow_open:raise ValueError('Unpaid conditional graph')
        return result|{'status':'OPEN'}
    if kind=='I':
        if term!={'kind':'I'}or out['status']!='EMPTY':raise ValueError('False conditional interval contradiction')
        return result|{'status':'EMPTY'}
    if out['status']=='EMPTY':raise ValueError('Use I for an empty graph')
    if kind=='A':
        if term!={'kind':'A'}or sa.fs.safe_port(out['aux_image'])is None:raise ValueError('False old alpha port')
        return result|{'status':'SAFE_ALPHA'}
    if kind not in ('C','H'):raise ValueError('Invalid conditional terminal')
    rows,boxes=db.rows_and_bounds(out['aux_image'],label,profile)
    margin=sa.inherited.dual_margin(rows,boxes,term)
    if (kind=='C'and margin>=0)or(kind=='H'and margin>0):raise ValueError('Unproved conditional terminal')
    return result|{'status':'EMPTY'if kind=='C'else'SAFE_ALPHA','margin':str(margin)}

def cheap_high(aux):
    """B01's proved conditional q-star budget; only for complete F>=gamma images."""
    k,r,s,t=[tb.I(*b)for b in aux[:4]]
    if min(k.lo,r.lo)<=0 or min(s.lo,t.lo)<0:raise ValueError('High-image coordinate bounds')
    pressure=r.hi*max(Q(0),2*r.hi-tb.GAMMA)**2/(4*tb.GAMMA**3)
    diff=max(Q(0),s.hi-t.lo,t.hi-s.lo);gap=max(Q(0),r.hi-max(s.lo,t.lo))
    direct=diff*gap/(2*r.lo*(r.lo+min(s.lo,t.lo)))
    epsilon=min(pressure,direct);threshold=Q(17,4132500)
    return {'status':'EMPTY_HIGH'if k.hi<=2 and epsilon<=threshold else'OPEN',
            'epsilon_upper':str(epsilon),'k_upper':str(k.hi),'r_upper':str(r.hi)}

def wrap(box,prefix,kind,**kw):return dict(kind=kind,**binding(box,prefix),prefix=prefix,**kw)

def verify(box,node,allow_open=False,cross_check=True):
    if not isinstance(node,dict):raise ValueError('Certificate object')
    kind=node.get('kind');prefix=node.get('prefix');expected={'kind',*binding(box,prefix),'prefix'}
    if kind=='B42':expected|={'method','symmetries'}
    elif kind=='C42':expected.add('children')
    else:raise ValueError('Wrong V42 wrapper kind')
    if set(node)!=expected:raise ValueError('Unknown or missing V42 fields')
    for k,v in binding(box,prefix).items():
        if node.get(k)!=v:raise ValueError('Wrong V42 '+k)
    base=endpoint(box,prefix,cross_check)
    if base['status']!='OPEN'or base.get('aux_image')is None:
        raise ValueError('Wrapper requires a still-open certified endpoint; use original terminal otherwise')
    aux=base['aux_image'];ans={'prefix_waves':base['waves'],'prefix_bounds':base['bounds'],
        'endpoint_sha256':canonical_hash(aux),'rule':RULE}
    if kind=='B42':
        if node['method'] not in ('legacy','one_slack')or type(node['symmetries'])is not bool:raise ValueError('Port options')
        require_gain();cheap=cheap_high(aux)
        port=tb.check_box(aux,centers(),node['symmetries'],node['method'])
        status='EMPTY_HIGH'if cheap['status']=='EMPTY_HIGH'else port['status']
        if status=='OPEN'and not allow_open:raise ValueError('Unpaid B42 port')
        return ans|dict(status=status,cheap=cheap,port=port)
    _,_,sa=v41_api();children=node['children']
    if not isinstance(children,dict)or set(children)!=set(sa.fs.GRAPH_LABELS):raise ValueError('All 189 conditional graphs required')
    counts={'EMPTY':0,'SAFE_ALPHA':0,'OPEN':0};waves=bounds=0
    for label in sa.fs.GRAPH_LABELS:
        val=child_replay(aux,children[label],label,cross_check,allow_open)
        counts[val['status']]+=1;waves+=val['waves'];bounds+=val['bounds']
    status='OPEN'if counts['OPEN']else'SAFE_ALPHA'if counts['SAFE_ALPHA']else'EMPTY_HIGH'
    return ans|dict(status=status,children=counts,conditional_waves=waves,conditional_bounds=bounds)

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('box');ap.add_argument('certificate');ap.add_argument('--allow-open',action='store_true');ap.add_argument('--output');a=ap.parse_args()
    b=json.loads(Path(a.box).read_text());b=b['box']if isinstance(b,dict)else b
    try:r=verify(b,json.loads(Path(a.certificate).read_text()),a.allow_open)
    except Exception as e:print(json.dumps(dict(status='REJECTED',error=str(e))));raise SystemExit(2)
    text=json.dumps(r,indent=2)
    if a.output:Path(a.output).write_text(text+'\n')
    else:print(text)
