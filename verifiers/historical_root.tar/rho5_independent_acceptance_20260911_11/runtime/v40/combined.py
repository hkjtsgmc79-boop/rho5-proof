"""V40 unified source-preserving contraction, exact quotient range and
homogeneous prefix/source consequences. Only potential canonical maximum
images are contracted; no old V39 accepting semantics is replaced.
"""
from homogeneous import *
from sharp_prefix import sharp_bounds

def contract_combined(parent,label,rounds=8):
 out=contract_full(parent,label)
 if out['status']=='EMPTY':return out
 b=[I(*x)for x in out['aux_image']];hom=homogeneous_rows(label);new=projective_data(label)[3]
 try:
  for it in range(rounds):
   prev=[x.data()for x in b]
   sharp_bounds(b,label)
   propagate(b,hom+new+projected_range_rows(b,label)+CHARTS[label][0]+BASE_POLYS)
   direct_bounds(b,label);reconstruct_tail(b)
   hc=high_contract(b,rounds=2)
   if hc['status']=='EMPTY':raise Empty(hc['reason'])
   for i,v in enumerate(hc['aux_image']):meet(b,i,Q(v[0]),Q(v[1]))
   no=strict_impossible(label,b)
   if no:raise Empty(no)
   if prev==[x.data()for x in b]:break
  return {'status':'BOUNDED','aux_image':[x.data()for x in b],'rounds':it+1}
 except Empty as err:return {'status':'EMPTY','reason':str(err)}
