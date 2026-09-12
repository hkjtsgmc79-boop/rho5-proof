"""V40 exact endpoint ranges for a positive/nonpositive prefix basis.
No quotient is taken at a nonpositive denominator. Unbounded limits retain
existing physical bounds. The ordered coefficient box is an outer domain.
"""
from projective_graph import *

def pair_ranges(ai,bi,aj,bj):
 # Return independently justified extrema when finite. Actual coefficients
 # lie in ai>=aj>=0, bi>0>=bj, ai>0, aj>0; closure is used for bounds.
 if not(ai.lo>=0 and aj.lo>=0 and bi.lo>=0 and bj.hi<=0):return {}
 if ai.hi<aj.lo:raise Empty('ordered_coefficient_box_empty')
 def ratp(a,b,c,d):
  den=c*b-a*d
  return (b-d)/den if den>0 else None
 def rate(a,b,c,d):
  den=c*b-a*d
  return (a-c)/den if den>0 else None
 amin=max(ai.lo,aj.lo);amax=ai.hi;jmin=aj.lo;jmax=min(aj.hi,ai.hi)
 out={'p_lower':ratp(amax,bi.lo,jmax,bj.lo),
      'p_upper':ratp(amin,bi.hi,jmin,bj.hi),
      'e_upper':rate(amax,bi.lo,jmin,bj.hi)}
 if ai.lo<=aj.hi:out['e_lower']=Q(0)
 else:out['e_lower']=rate(ai.lo,bi.hi,aj.hi,bj.lo)
 return out

def sharp_bounds(b,label):
 parts=label.split('|')[1].split(':')
 if parts[0]!='N':return
 ai,bi=row_coeff(parts[1]);aj,bj=row_coeff(parts[2])
 a=interval(ai,b);bb=interval(bi,b);aa=interval(aj,b);b2=interval(bj,b)
 out=pair_ranges(a,bb,aa,b2)
 for key,idx,side in [('p_lower',8,'lo'),('p_upper',8,'hi'),('e_lower',9,'lo'),('e_upper',9,'hi')]:
  v=out.get(key)
  if v is not None:meet(b,idx,**{side:v})

def contract_sharp(parent,label,rounds=8):
 out=contract_full(parent,label)
 if out['status']=='EMPTY':return out
 b=[I(*x)for x in out['aux_image']]
 try:
  for it in range(rounds):
   prev=[x.data()for x in b]
   sharp_bounds(b,label)
   propagate(b,CHARTS[label][0]+BASE_POLYS)
   direct_bounds(b,label);reconstruct_tail(b)
   hc=high_contract(b,rounds=2)
   if hc['status']=='EMPTY':raise Empty(hc['reason'])
   for i,v in enumerate(hc['aux_image']):meet(b,i,Q(v[0]),Q(v[1]))
   no=strict_impossible(label,b)
   if no:raise Empty(no)
   if prev==[x.data()for x in b]:break
  return {'status':'BOUNDED','aux_image':[x.data()for x in b],'rounds':it+1}
 except Empty as e:return {'status':'EMPTY','reason':str(e)}
