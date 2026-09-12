"""V40 prototype: preserve a SAME canonical prefix image while propagating
all universal physical rows, instead of testing their interval sign only.
No new source equation/continuous variable/product is introduced.
"""
import bootstrap
from graph_protocol import *

def contract_full(parent,label,rounds=8):
 old=contract_chart(parent,label)
 if old['status']=='EMPTY':return old
 b=[I(*x)for x in old['aux_image']]
 try:
  for it in range(rounds):
   before=[x.data()for x in b]
   propagate(b,CHARTS[label][0]+BASE_POLYS)
   direct_bounds(b,label)
   reconstruct_tail(b)
   hc=high_contract(b,rounds=2)
   if hc['status']=='EMPTY':raise Empty(hc['reason'])
   for i,v in enumerate(hc['aux_image']):meet(b,i,Q(v[0]),Q(v[1]))
   no=strict_impossible(label,b)
   if no:raise Empty(no)
   if before==[x.data()for x in b]:break
  return {'status':'BOUNDED','aux_image':[x.data()for x in b],'rounds':it+1}
 except Empty as e:return {'status':'EMPTY','reason':str(e)}
