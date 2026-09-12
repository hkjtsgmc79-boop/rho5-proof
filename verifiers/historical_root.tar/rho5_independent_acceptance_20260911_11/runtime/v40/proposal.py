"""Optional untrusted float LP proposal; exact acceptance is separate."""
import os
for name in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[name]='1'
import numpy as np
from scipy.optimize import linprog
from linear_certificate import dual_margin,FI

def propose_rows(rows,boxes):
 n=len(boxes);center=np.array([float((b.lo+b.hi)/2)for b in boxes]);half=np.array([float((b.hi-b.lo)/2)for b in boxes]);mat=np.zeros((len(rows),n));rhs=np.zeros(len(rows))
 for i,(aa,bb)in enumerate(rows):
  rhs[i]=float(bb)
  for j,c in aa.items():mat[i,j]=float(c)
 bb=rhs-mat@center;aa=mat*half;norm=np.maximum(1e-9,np.maximum(abs(bb),np.max(abs(aa),axis=1)));aa/=norm[:,None];bb/=norm
 def rat(v,kind):
  if not np.all(np.isfinite(v)):return None
  for sc in (10**7,10**10,10**13):
   ws=[max(0,int(round(float(x)*sc)))for x in v];rec={'kind':kind,'weights':[[i,w]for i,w in enumerate(ws)if w]}
   if kind=='H':rec['objective_weight']=sc
   if not rec['weights']:continue
   try:m=dual_margin(rows,boxes,rec)
   except (ValueError,ZeroDivisionError):continue
   if m<0 if kind=='C' else m<=0:return rec
  return None
 obj=np.zeros(n+1);obj[-1]=1
 res=linprog(obj,A_ub=np.column_stack((aa,-np.ones(len(rows)))),b_ub=bb,bounds=[(-1,1)]*n+[(0,None)],method='highs',options={'time_limit':2})
 if res.success and res.fun>1e-10:
  rec=rat(-res.ineqlin.marginals/norm,'C')
  if rec:return rec
 obj=np.zeros(n);obj[FI]=-half[FI]
 res=linprog(obj,A_ub=aa,b_ub=bb,bounds=[(-1,1)]*n,method='highs',options={'time_limit':2})
 if res.success:return rat(-res.ineqlin.marginals/norm,'H')
 return None
