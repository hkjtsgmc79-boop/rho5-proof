"""Finite diagnostic: same interval propagation but NO maximality charts.
Not an alternative proof rule, no original tree mutation.
"""
import json,time
from collections import Counter
from graph_contract import *
from relaxation import rows_and_bounds,margin

def baseline_contract(parent):
 b=[I(*v)for v in parent['aux_image']]
 try:
  for _ in range(4):
   propagate(b,PREFIX_BASE);reconstruct_tail(b)
   h=high_contract(b,rounds=2)
   if h['status']=='EMPTY':raise Empty(h['reason'])
   for i,v in enumerate(h['aux_image']):meet(b,i,Q(v[0]),Q(v[1]))
   for name,p in BASE_POLYS:
    if interval(p,b).hi<0:raise Empty(name)
  return {'status':'BOUNDED','aux_image':[v.data()for v in b]}
 except Empty as err:return {'status':'EMPTY','reason':str(err)}

def run():
 import discover
 # The proposal routine receives the universal 106 rows, without graph contacts.
 # Every proposed C/H is checked against the original rational margin routine.
 old_rows,old_margin=discover.rows_for,discover.exact_margin
 discover.rows_for=lambda aux,label:rows_and_bounds(aux)
 discover.exact_margin=lambda aux,label,record:margin(aux,record)
 results=[];start=time.monotonic()
 try:
  samples=json.loads((paths.ROOT/'inputs/diagnostics/audit_final/SAMPLE_CONTROLS.json').read_text())
  for item in samples:
   out=baseline_contract(parent_enclosure(item['box']))
   if out['status']=='EMPTY':kind='INTERVAL';rec=None
   else:
    rec=discover.lp_propose(out['aux_image'],'unused');kind=rec['kind']if rec else'UNRESOLVED'
   results.append({'sample':item['sample'],'kind':kind,'certificate':rec})
 finally:discover.rows_for,discover.exact_margin=old_rows,old_margin
 result={'comparison':'same four-pass ordinary prefix/tail contraction, without maximality graphs',
   'counts':dict(Counter(r['kind']for r in results)),'seconds':time.monotonic()-start,'records':results,
   'unresolved_means_no_certificate_found':True,'not_a_global_performance_claim':True}
 (paths.ROOT/'evidence/ablation.json').write_text(json.dumps(result,indent=2)+'\n')
 return result
if __name__=='__main__':print(json.dumps(run(),indent=2))
