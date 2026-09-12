import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1');os.environ.setdefault('OMP_NUM_THREADS','1')
import sys,ctypes,json,time
from pathlib import Path
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
from math import gcd
ROOT=Path(__file__).resolve().parent;S=1<<32
key=sys.argv[1]; cap=int(sys.argv[2]) if len(sys.argv)>2 else 100000
sp=json.loads((ROOT/'certificates'/f'{key}.json').read_text());n=len(sp['variables'])
lib=ctypes.CDLL(str(ROOT/f'linear_{key}.so'));lib.assess.argtypes=[ctypes.POINTER(ctypes.c_longlong)]*3;m=lib.nr()
box_t=ctypes.c_longlong*(2*n);rad_t=ctypes.c_longlong*n;c_t=ctypes.c_longlong*(m*(n+1))

def getrows(buf,rad):
 ai=[[int(buf[j*(n+1)+i])*int(rad[i])for i in range(n)]for j in range(m)]
 bi=[int(buf[j*(n+1)+n])*S for j in range(m)]
 den=[max(abs(b),max(map(abs,a))) or 1 for a,b in zip(ai,bi)]
 return ai,bi,den

def exact_cut(ai,bi,den,weights):
 # One common integer denominator permits an independent exact Farkas check.
 ww=[(i,F(w,den[i]))for i,w in weights if w>0]
 C=sum((w*bi[i]for i,w in ww),F(0));G=[sum((w*ai[i][j]for i,w in ww),F(0))for j in range(n)]
 return C+sum(map(abs,G),F(0))

def dual_cut(ai,bi,den):
 aa=np.array([[a/d for a in row]+[1.]for row,d in zip(ai,den)]);bb=np.array([b/d for b,d in zip(bi,den)])
 obj=np.zeros(n+1);obj[-1]=1
 rr=linprog(obj,A_ub=-aa,b_ub=bb,bounds=[(-1,1)]*n+[(None,None)],method='highs',options={'presolve':True})
 if not rr.success or rr.fun<=1e-10:return None
 lam=-rr.ineqlin.marginals;weights=[(i,int(round(float(w)*(1<<26))))for i,w in enumerate(lam) if w>1e-12 and int(round(float(w)*(1<<26)))>0]
 if not weights:return None
 if exact_cut(ai,bi,den,weights)<0:return weights
 # Larger positive rational multipliers for exceptionally tight separations.
 weights=[(i,int(round(float(w)*(1<<42))))for i,w in enumerate(lam) if w>1e-14 and int(round(float(w)*(1<<42)))>0]
 return weights if exact_cut(ai,bi,den,weights)<0 else None

if __name__=='__main__':
 start=time.time();todo=[(sp['root_box'],0)];nodes=leaves=fl=0;depth=0
 with (ROOT/'certificates'/f'{key}.lp_proof').open('w') as f:
  f.write('V24-EXACT-MEAN-FARKAS-1 32\n')
  while todo and nodes<cap:
   box,dep=todo.pop();nodes+=1;depth=max(depth,dep);buf=box_t(*[v for pair in box for v in pair]);rad=rad_t();coeff=c_t();status=lib.assess(buf,rad,coeff)
   if status<0:raise RuntimeError('kernel error')
   if status==1:f.write('L\n');leaves+=1;continue
   box=[[int(buf[2*i]),int(buf[2*i+1])]for i in range(n)]
   weights=None
   if status==0:
    ai,bi,den=getrows(coeff,rad);weights=dual_cut(ai,bi,den)
   if weights is not None:
    f.write('F '+str(len(weights))+' '+' '.join(f'{i} {w}' for i,w in weights)+'\n');leaves+=1;fl+=1
   else:
    idx=max(range(8),key=lambda i:box[i][1]-box[i][0]);lo,hi=box[idx]
    if hi-lo<=1:raise RuntimeError('unresolved precision leaf')
    mid=lo+(hi-lo)//2;f.write(f'B {idx} {mid}\n');right=[row[:]for row in box];box[idx][1]=mid;right[idx][0]=mid;todo.append((right,dep+1));todo.append((box,dep+1))
   if nodes%100==0:print(key,'nodes',nodes,'pending',len(todo),'farkas',fl,'depth',dep,'sec',time.time()-start,flush=True)
  if todo:
   f.write('U\n');raise RuntimeError('node cap; incomplete')
  f.write('END\n')
 print('UNSAT_EXACT',key,'nodes',nodes,'leaves',leaves,'Farkas',fl,'depth',depth,'sec',time.time()-start,flush=True)
 (ROOT/f'{key}_stats.json').write_text(json.dumps(dict(key=key,nodes=nodes,leaves=leaves,farkas=fl,max_depth=depth,seconds=time.time()-start),indent=2))
