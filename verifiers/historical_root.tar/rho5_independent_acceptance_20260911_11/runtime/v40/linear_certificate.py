from full_source import *

def dual_margin(rows,boxes,record):
 kind=record.get('kind');expected={'kind','weights'}if kind=='C'else{'kind','weights','objective_weight'}
 if kind not in ('C','H')or set(record)!=expected:raise ValueError('bad dual schema')
 coeff=[Q(0)]*len(boxes);rhs=Q(0);seen=set()
 w=record.get('weights')
 if not isinstance(w,list)or not w:raise ValueError('empty support')
 for pair in w:
  if not isinstance(pair,list)or len(pair)!=2:raise ValueError('bad pair')
  idx,ww=pair
  if type(idx)is not int or type(ww)is not int or not 0<=idx<len(rows)or ww<=0 or idx in seen:raise ValueError('bad index or weight')
  seen.add(idx);a,b=rows[idx];rhs+=ww*b
  for i,c in a.items():coeff[i]+=ww*c
 if kind=='H':
  t=record['objective_weight']
  if type(t)is not int or t<=0:raise ValueError('bad height multiplier')
  coeff[FI]-=t
 val=rhs-sum(min(c*b.lo,c*b.hi)for c,b in zip(coeff,boxes))
 if kind=='H':val-=t*ALPHA
 return val
