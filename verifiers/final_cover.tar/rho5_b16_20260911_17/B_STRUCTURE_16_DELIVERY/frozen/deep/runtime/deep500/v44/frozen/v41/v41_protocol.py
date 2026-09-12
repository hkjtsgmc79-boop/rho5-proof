"""U41: unconditioned proof. G41: disjunction of all 189 guarded charts.
A conditional trace on its own can never be accepted as an unconditional leaf.
"""
from pathlib import Path
import hashlib,json
from source_access import ROOT,SOURCE,IDENTITY,fs,inherited
from dual_box import replay_trace
RULE='V41_EXACT_DUAL_BOX_RECONSTRUCTION_V1'
RULE_FILES=('source_access.py','pivot_windows.py','dual_box.py','v41_protocol.py')
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def rule_identity():
    d={n:sha(ROOT/n)for n in RULE_FILES}
    d['received_light']=IDENTITY['received_zip_sha256']
    d['alpha']=sha(SOURCE/'dependency/alpha.json')
    return hashlib.sha256(json.dumps(d,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def bind(box):
    box=inherited.validate_box(box)
    return dict(rule=RULE,rule_identity=rule_identity(),model_sha256=IDENTITY['b17_model_sha256'],
                round50_reported_root_sha256=IDENTITY['reported_root_sha256'],box_sha256=fs.box_hash(box))
def wrap(box,trace):return dict(kind='U41',**bind(box),trace=trace)
def verify(box,node,allow_open=False,cross_check=False):
    box=inherited.validate_box(box)
    if not isinstance(node,dict):raise ValueError('Invalid certificate')
    kind=node.get('kind');keys={'kind',*bind(box)}
    if kind=='U41':keys.add('trace')
    elif kind=='G41':keys.add('children')
    else:raise ValueError('Not a V41 parent certificate')
    if set(node)!=keys:raise ValueError('Unknown/missing parent fields')
    for k,v in bind(box).items():
        if node.get(k)!=v:raise ValueError('Wrong '+k)
    if kind=='U41':
        result=replay_trace(box,node['trace'],cross_check=cross_check,allow_open=allow_open)
        result.pop('aux_image',None)
        return result
    children=node['children']
    if not isinstance(children,dict)or set(children)!=set(fs.GRAPH_LABELS):raise ValueError('Incomplete conditional disjunction')
    parent=fs.parent_enclosure(box);counts={'EMPTY':0,'SAFE':0,'OPEN':0};bounds=0;waves=0
    for lab in fs.GRAPH_LABELS:
        rec=children[lab]
        if not isinstance(rec,dict):raise ValueError('Bad child')
        if rec.get('engine')=='V40'and set(rec)=={'engine','record'}:
            status=inherited.verify_child_new(parent,lab,rec['record'],allow_open)
        elif rec.get('engine')=='V41'and set(rec)=={'engine','trace'}:
            val=replay_trace(box,rec['trace'],label=lab,cross_check=cross_check,allow_open=allow_open)
            status=val['status'];bounds+=val['bounds'];waves+=val['waves']
        elif rec=={'engine':'OPEN'}and allow_open:status='OPEN'
        else:raise ValueError('Invalid or unpaid graph')
        counts[status]+=1
    return dict(status='OPEN'if counts['OPEN']else'SAFE'if counts['SAFE']else'EMPTY',children=counts,bounds=bounds,waves=waves)
if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('box');ap.add_argument('certificate');ap.add_argument('--allow-open',action='store_true');ap.add_argument('--cross-check',action='store_true');a=ap.parse_args()
    b=json.loads(Path(a.box).read_text());b=b['box']if isinstance(b,dict)else b
    try:out=verify(b,json.loads(Path(a.certificate).read_text()),a.allow_open,a.cross_check)
    except Exception as exc:print(json.dumps(dict(status='REJECTED',error=str(exc))));raise SystemExit(2)
    print(json.dumps(out,indent=2))
