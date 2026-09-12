"""Replay stored positive ablation certificates. OPEN is a diagnostic result,
not proof that no certificate exists. No LP is used in this replay.
"""
import json
from protocol import *

def check(parent,label,rec,rounds):
 if rec=={'kind':'O'}:return 'O'
 z=contract_full(parent,label,rounds=rounds);kind=rec.get('kind')
 if kind=='I':assert rec=={'kind':'I'}and z['status']=='EMPTY';return kind
 assert z['status']=='BOUNDED'
 if kind=='A':assert rec=={'kind':'A'}and safe_port(z['aux_image'])is not None;return kind
 assert kind in('C','H');m=dual_margin(*rows_for(z['aux_image'],label),rec)
 assert (m<0 if kind=='C'else m<=0);return kind

def run():
 src=bootstrap.ROOT/'evidence/ablation';full={}
 for f in sorted((src/'full8').glob('sample_*.json')):
  obj=json.loads(f.read_text());full[obj['sample_id']]=obj
 assert len(full)==64
 closed=[i for i,o in full.items()if all(r['kind']!='O'for r in o['children'].values())]
 assert len(closed)==49
 # Exact-replay all 90 formerly unpaid children of the 15 unclosed parents
 # with the extended 22-round ordinary propagation budget.
 checked=opens=paid=0;still=[]
 for i in sorted(set(range(64))-set(closed)):
  row=full[i];parent=parent_enclosure(row['box']);ab=json.loads((src/'full22'/f'sample_{i:02d}.json').read_text())
  old_open={g for g,r in row['children'].items()if r['kind']=='O'}
  assert set(ab['children'])==old_open
  oo=0
  for g,r in ab['children'].items():
   kind=check(parent,g,r,22);checked+=1
   if kind=='O':opens+=1;oo+=1
   else:paid+=1
  if oo:still.append(i)
 assert checked==90 and len(still)==15
 # Parent 47/48 exact V40 successes are replayed separately by verify_all.
 return {'ordinary_full8_complete_parents':49,'ordinary_full22_still_incomplete_parents':len(still),
   'extended_budget_tested_formerly_open_subgraphs':checked,'extended_budget_proved_additional_children':paid,
   'extended_budget_unpaid_children':opens,'comparison_is_bounded_search_not_nonexistence_proof':True,
   'extra_V40_complete_sample_ordinals':[47,48]}
if __name__=='__main__':print(json.dumps(run(),indent=2))
