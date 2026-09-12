"""Versioned V39 adapters. Original E/C/H and high_value_v1 remain unchanged.
V is four-round ordinary propagation; G is all189 complete conditional charts.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,sys
ROOT=Path(__file__).resolve().parent
import tree_protocol as tp
import native_backend as old_native
from high_value_reference import verify_leaf as old_fraction
sys.path.insert(0,str(ROOT/'v39'))
import graph_protocol as gp
import ablation
import relaxation
ORDINARY='V39_ORDINARY_PROPAGATION_V1'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ordinary_identity():
    files={n:sha(ROOT/'v39'/n)for n in('ablation.py','graph_contract.py','prefix_graph.py','graph_protocol.py')}
    files['parent_rule']=gp.rule_identity()
    return hashlib.sha256(json.dumps(files,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def ordinary_wrap(box,record):
    return {'kind':'V','rule':ORDINARY,'rule_identity':ordinary_identity(),'box_sha256':gp.box_hash(box),'record':record}
def verify_leaf(box,node,backend='native'):
    if not isinstance(node,dict):raise ValueError('invalid leaf record')
    kind=node.get('kind')
    if kind in('E','C','H'):return old_native.verify_leaf(box,node)if backend=='native'else old_fraction(box,node)
    if kind=='G':
        if set(node)!={'kind','cover'}or not isinstance(node['cover'],dict):raise ValueError('bad G schema')
        result=gp.verify_cover(box,node['cover'])
        if result['open_charts']:raise ValueError('unpaid G')
        return 'SAFE'if result['alpha_safe_charts']else'EMPTY'
    if kind!='V' or set(node)!={'kind','rule','rule_identity','box_sha256','record'}:raise ValueError('unknown leaf/schema')
    if node['rule']!=ORDINARY or node['rule_identity']!=ordinary_identity()or node['box_sha256']!=gp.box_hash(box):raise ValueError('ordinary version or box mismatch')
    record=node['record']
    if not isinstance(record,dict):raise ValueError('bad V certificate')
    parent=gp.parent_enclosure(box)
    out=parent if parent['status']=='EMPTY'else ablation.baseline_contract(parent)
    if record.get('kind')=='I':
        if set(record)!={'kind'}or out['status']!='EMPTY':raise ValueError('unproved V interval exclusion')
        return 'EMPTY'
    if out['status']=='EMPTY':raise ValueError('use I for deterministic empty')
    if record.get('kind')=='A':
        if set(record)!={'kind'}or gp.safe_port(out['aux_image'])is None:raise ValueError('unproved V alpha port')
        return 'SAFE'
    if record.get('kind')not in('C','H'):raise ValueError('unknown V certificate')
    expected={'kind','weights'}if record['kind']=='C'else{'kind','weights','objective_weight'}
    if set(record)!=expected:raise ValueError('V C/H schema mismatch')
    value=relaxation.margin(out['aux_image'],record)
    if record['kind']=='C'and value<0:return 'EMPTY'
    if record['kind']=='H'and value<=0:return 'SAFE'
    raise ValueError('invalid V exact margin')
def ordinary_propose(box):
    import discover
    parent=gp.parent_enclosure(box)
    out=parent if parent['status']=='EMPTY'else ablation.baseline_contract(parent)
    if out['status']=='EMPTY':return ordinary_wrap(box,{'kind':'I'})
    if gp.safe_port(out['aux_image'])is not None:return ordinary_wrap(box,{'kind':'A'})
    previous_rows,previous_margin=discover.rows_for,discover.exact_margin
    try:
        discover.rows_for=lambda aux,label:relaxation.rows_and_bounds(aux)
        discover.exact_margin=lambda aux,label,record:relaxation.margin(aux,record)
        record=discover.lp_propose(out['aux_image'],'unused')
    finally:discover.rows_for,discover.exact_margin=previous_rows,previous_margin
    return ordinary_wrap(box,record)if record else None
def structure(data):
    if data.get('model_sha256')!=sha(tp.MODEL)or data.get('task')is not None or data.get('root_path')!='':raise ValueError('wrong original root ownership')
    nodes=data.get('nodes')
    if not isinstance(nodes,list)or not nodes:raise ValueError('empty tree')
    slots=1
    for n in nodes:
        if not isinstance(n,dict)or slots<=0:raise ValueError('bad tree envelope')
        kind=n.get('kind')
        if kind=='S':
            if set(n)!={'kind','axis'}or type(n['axis'])is not int or not 0<=n['axis']<17:raise ValueError('bad split')
            slots+=1
        elif kind=='O':
            if set(n)!={'kind'}:raise ValueError('bad O')
            slots-=1
        elif kind in('E','C','H','V','G'):slots-=1
        else:raise ValueError('unknown node')
    if slots:raise ValueError('truncated tree')
    return tp.root_box()
def binding():
    return {'schema':'ROUND49_V39_ADAPTER_V1','original_model_sha256':sha(tp.MODEL),'v39_rule_identity':gp.rule_identity(),
            'ordinary_rule_identity':ordinary_identity(),'adapter_sha256':sha(Path(__file__)),'v39_manifest_sha256':sha(ROOT/'v39/MANIFEST.json'),
            'old_source_manifest_sha256':sha(ROOT/'HIGH_VALUE_SOURCE_MANIFEST.json'),'macro_ledger':'14/15','whole_B_closed':False}
