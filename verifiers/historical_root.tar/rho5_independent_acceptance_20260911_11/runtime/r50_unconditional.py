"""Versioned eight-round FULL universal contraction, no conditional contacts.
Every true canonical image satisfies the 106 baseline rows. Propagating those
rows preserves it by V40 Theorem 2, as does the inherited same-source tail
reconstruction. Original 38-product rows remain the C/H certificate dictionary.
"""
from pathlib import Path
import hashlib,json
import r49_protocol as old
gp=old.gp;Q=old.Q;ROOT=Path(__file__).resolve().parent
RULE='ROUND50_UNCONDITIONAL_FULL_SOURCE_8_V1'
def identity():
 data={n:old.sha(ROOT/n)for n in ('r50_unconditional.py','R49_SOURCE_MANIFEST.json')}
 return hashlib.sha256(json.dumps(data,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def contract(box):
 parent=gp.parent_enclosure(box)
 out=parent if parent['status']=='EMPTY'else old.ablation.baseline_contract(parent)
 if out['status']=='EMPTY':return out
 b=[gp.I(*x)for x in out['aux_image']]
 try:
  for _ in range(8):
   before=[x.data()for x in b]
   gp.propagate(b,gp.BASE_POLYS);gp.reconstruct_tail(b)
   h=gp.high_contract(b,rounds=2)
   if h['status']=='EMPTY':raise gp.Empty(h['reason'])
   for i,v in enumerate(h['aux_image']):gp.meet(b,i,Q(v[0]),Q(v[1]))
   if before==[x.data()for x in b]:break
  return {'status':'BOUNDED','aux_image':[x.data()for x in b]}
 except gp.Empty as err:return {'status':'EMPTY','reason':str(err)}
def wrap(box,proof):return {'kind':'U40','rule':RULE,'rule_identity':identity(),'box_sha256':gp.box_hash(box),'proof':proof}
def verify(box,node):
 if set(node)!={'kind','rule','rule_identity','box_sha256','proof'}or node['kind']!='U40' or node['rule']!=RULE or node['rule_identity']!=identity()or node['box_sha256']!=gp.box_hash(box):raise ValueError('bad U40 binding')
 out=contract(box);proof=node['proof']
 if not isinstance(proof,dict):raise ValueError('bad U40 proof')
 if proof.get('kind')=='I':
  if proof!={'kind':'I'}or out['status']!='EMPTY':raise ValueError('false U40 empty')
  return 'EMPTY'
 if out['status']=='EMPTY':raise ValueError('use I')
 if proof.get('kind')=='A':
  if proof!={'kind':'A'}or gp.safe_port(out['aux_image'])is None:raise ValueError('false U40 alpha')
  return 'SAFE'
 if proof.get('kind')not in ('C','H'):raise ValueError('unknown U40 proof')
 margin=old.relaxation.margin(out['aux_image'],proof)
 if proof['kind']=='C'and margin<0:return 'EMPTY'
 if proof['kind']=='H'and margin<=0:return 'SAFE'
 raise ValueError('invalid U40 margin')
def propose(box):
 import discover
 out=contract(box)
 if out['status']=='EMPTY':return wrap(box,{'kind':'I'})
 if gp.safe_port(out['aux_image'])is not None:return wrap(box,{'kind':'A'})
 rows,margin=discover.rows_for,discover.exact_margin
 try:
  discover.rows_for=lambda aux,label:old.relaxation.rows_and_bounds(aux)
  discover.exact_margin=lambda aux,label,rec:old.relaxation.margin(aux,rec)
  proof=discover.lp_propose(out['aux_image'],'unused')
 finally:discover.rows_for,discover.exact_margin=rows,margin
 return wrap(box,proof)if proof else None
