"""Discovery only: every accepted record has an exact integer check.
The independent verifier re-evaluates intervals and all implications.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
os.environ.setdefault('OMP_NUM_THREADS','1')
import ctypes, json, gzip, time, math, argparse
from pathlib import Path
from fractions import Fraction as Q
import numpy as np
from scipy.optimize import linprog
BASE=Path(__file__).resolve().parent
S=1<<40; N=6
lib=ctypes.CDLL(str(BASE/'libeval.so'))
ptr=np.ctypeslib.ndpointer(dtype=np.int64,flags='C_CONTIGUOUS')
lib.eval.argtypes=[ptr,ptr,ctypes.c_int64,ctypes.c_int64,ptr,ptr]

def evaluate(lo,hi,f):
    b=np.zeros((37,2),dtype=np.int64); rows=np.zeros((37,7),dtype=np.int64)
    rc=lib.eval(np.array(lo,dtype=np.int64),np.array(hi,dtype=np.int64),f.numerator,f.denominator,b,rows)
    if rc:raise RuntimeError(('interval evaluation failure',rc,lo,hi))
    m=36 if b[36,0]>=0 else 35
    return b,rows[:m]

def weighted(rows,w):
    return [sum(int(rows[j,i])*ww for j,ww in w) for i in range(7)]

def candidates(lam):
    lam=np.maximum(lam,0)
    mx=max(lam)
    if mx<=0:return
    lam=lam/mx
    for scale in [10**6,10**9,10**12]:
        w=[[int(j),int(round(float(a)*scale))] for j,a in enumerate(lam) if a*scale>=.5]
        if w:yield w

def combo(rows,lam):
    for w in candidates(lam):
        z=weighted(rows,w)
        if z[0]+sum(abs(a) for a in z[1:])<0:return w
    return None

def contractor_cut(rows,lam,dim,side,lo,hi):
    c=[(l+h)//2 for l,h in zip(lo,hi)];rad=[max(h-cc,cc-l) for l,h,cc in zip(lo,hi,c)]
    if rad[dim]==0:return
    for w in candidates(lam):
        z=weighted(rows,w); A=z[dim+1]
        if (side=='lo' and A<=0) or (side=='hi' and A>=0):continue
        B=z[0]+sum(abs(z[i+1]) for i in range(6) if i!=dim)
        # Intentionally retreat 2% of the current width from the exact bound.
        bound=Q(c[dim])-Q(rad[dim]*B,A)
        if side=='lo': cut=math.floor(bound)-max(1,(hi[dim]-lo[dim])//50)
        else:cut=math.ceil(bound)+max(1,(hi[dim]-lo[dim])//50)
        if not lo[dim]<cut<hi[dim]:continue
        gain=(cut-lo[dim] if side=='lo' else hi[dim]-cut)/(hi[dim]-lo[dim])
        if gain<.1:continue
        if B*rad[dim]+A*(cut-c[dim])>=0:continue
        return [dim,side,cut,w]

def solve(lo,hi,f,do_contract=True):
    bd,rows=evaluate(lo,hi,f); m=len(rows)
    active=36 if bd[36,0]>=0 else 35
    direct=np.nonzero(bd[:active,1]<0)[0]
    if len(direct):return {'kind':'I','guard':int(direct[0])}
    # All returned row entries are exact integer coefficients in one scale.
    for j,row in enumerate(rows):
        if int(row[0])+sum(abs(int(a)) for a in row[1:])<0:
            return {'kind':'F','weights':[[j,1]]}
    vals=rows.astype(float)/S
    scales=np.maximum(np.maximum(np.sum(abs(vals[:,1:]),axis=1),abs(vals[:,0])),1e-16)
    vals=vals/scales[:,None]
    AA=-vals[:,1:];bb=vals[:,0]
    phase=linprog([0.]*6+[-1.],A_ub=np.column_stack([AA,np.ones(m)]),b_ub=bb,
        bounds=[(-1,1)]*6+[(None,None)],method='highs',options={'presolve':True})
    if not phase.success:raise RuntimeError(('phase LP',phase.message))
    if -phase.fun < -1e-9:
        w=combo(rows,-phase.ineqlin.marginals/scales)
        if w:return {'kind':'F','weights':w}
    if not do_contract:return None
    if -phase.fun<-1e-7:return None
    cuts=[]
    # Twelve coordinate LPs give candidate implications; all are independently checked.
    for d in range(6):
        if hi[d]-lo[d]<=2:continue
        for side,sgn in [('lo',1),('hi',-1)]:
            obj=np.zeros(6);obj[d]=sgn
            ans=linprog(obj,A_ub=AA,b_ub=bb,bounds=[(-1,1)]*6,
                       method='highs',options={'presolve':True})
            if not ans.success:continue
            if ans.fun<-.75:continue
            cc=contractor_cut(rows,-ans.ineqlin.marginals/scales,d,side,lo,hi)
            if cc:cuts.append(cc)
    if cuts:return {'kind':'C','cuts':cuts}
    return None


def run_root(front,limit=300000,seconds=1800,contract=True):
    cp=json.loads((BASE/'RHO5_V26_REBUILT/global_localization_partial_checkpoint.json').read_text())
    root=next(x for x in cp['open_frontier'] if int(x['node'])==front)
    f=Q(cp['f']);lo=[int(Q(a)*S) for a in root['lo']];hi=[int(Q(a)*S) for a in root['hi']]
    tlo=[Q(x)*S for x in cp['target_lo']];thi=[Q(x)*S for x in cp['target_hi']]
    globalwidths=[float(Q(h)-Q(l))*S for l,h in zip(cp['root_lo'],cp['root_hi'])]
    out=BASE/'certs';out.mkdir(exist_ok=True)
    dst=out/f'front_{front}.jsonl.gz';fp=gzip.open(dst,'wt',encoding='utf-8')
    def write(rec):fp.write(json.dumps(rec,separators=(',',':'))+'\n')
    write({'format':'V28_EXACT_GRID_TREE_V1','front':front,'f':str(f),'grid_bits':40,'root_lo':lo,'root_hi':hi})
    stack=[(lo,hi,1,0)];counts={k:0 for k in ('I','F','C','B','Q','E','OPEN')};n=0;started=time.time(); maxdepth=0
    while stack:
        lo,hi,nid,depth=stack.pop();n+=1; maxdepth=max(maxdepth,depth)
        if n>limit or time.time()-started>seconds:
            write({'kind':'OPEN','node':nid,'lo':lo,'hi':hi});counts['OPEN']+=1
            for l,h,nn,dep in stack:write({'kind':'OPEN','node':nn,'lo':l,'hi':h});counts['OPEN']+=1
            stack.clear();break
        if any(lo[i]>hi[i] for i in range(6)):
            rec={'kind':'E'}
        elif all(lo[i]>=tlo[i] and hi[i]<=thi[i] for i in range(6)):
            rec={'kind':'Q'}
        else:
            rec=solve(lo,hi,f,contract)
        if rec is None:
            scores=[((hi[i]-lo[i])/globalwidths[i])*(1.0 if lo[i]<tlo[i] or hi[i]>thi[i] else .1) for i in range(6)]
            d=max(range(6),key=lambda i:scores[i]);mid=(lo[d]+hi[d])//2
            if not lo[d]<mid<hi[d]:raise RuntimeError('grid exhausted')
            rec={'kind':'B','axis':d,'cut':mid}
            lhi=list(hi);lhi[d]=mid;rlo=list(lo);rlo[d]=mid
            stack.append((rlo,hi,nid*2+1,depth+1));stack.append((lo,lhi,nid*2,depth+1))
        elif rec['kind']=='C':
            nlo=list(lo);nhi=list(hi)
            for d,side,cut,w in rec['cuts']:
                if side=='lo':nlo[d]=max(nlo[d],cut)
                else:nhi[d]=min(nhi[d],cut)
            # An empty child is itself sufficient, but use an explicit empty terminal.
            stack.append((nlo,nhi,nid*2,depth+1))
        counts[rec['kind']]+=1;rec['node']=nid;write(rec)
        if n%1000==0:
            status={'front':front,'processed':n,'stack':len(stack),'counts':counts,'seconds':time.time()-started,'maxdepth':maxdepth}
            (out/f'front_{front}_progress.json').write_text(json.dumps(status));print(status,flush=True);fp.flush()
    fp.close()
    status={'front':front,'processed':n,'stack':len(stack),'counts':counts,'seconds':time.time()-started,'maxdepth':maxdepth,'file':str(dst)}
    (out/f'front_{front}_result.json').write_text(json.dumps(status,indent=2)); print('FINISH',status,flush=True)
    return status

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--front',type=int,required=True);ap.add_argument('--seconds',type=int,default=1800);ap.add_argument('--limit',type=int,default=300000);ap.add_argument('--no-contract',action='store_true')
    a=ap.parse_args();run_root(a.front,a.limit,a.seconds,not a.no_contract)
