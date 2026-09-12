"""Independent rational C/H leaf verifier on the 24-coordinate canonical image.
No X-specific r-w objective, no fabricated packet, and no 18-contact assumptions.
SciPy is imported only by optional discovery, never by acceptance.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import isfinite
import json
from interval_capacity import I,oracle,ALPHA
ROOT=Path(__file__).parent
BASE=json.loads((ROOT/'models/B24_BASE.json').read_text())
NAMES=BASE['coordinate_order'];NV=len(NAMES);FI=NAMES.index('F')
LABELS=list(BASE['rows_ge_zero'])
PAIRS=sorted({tuple(t['monomial'])for row in BASE['rows_ge_zero'].values()for t in row if len(t['monomial'])==2})
PAIR_INDEX={p:NV+i for i,p in enumerate(PAIRS)};N=NV+len(PAIRS)

def rows_and_bounds(aux):
    boxes=[v if isinstance(v,I)else I(*v)for v in aux]
    assert len(boxes)==NV
    boxes += [boxes[i]*boxes[j] for i,j in PAIRS]
    rows=[]
    for label in LABELS:
        co={};rhs=Q(0)
        for term in BASE['rows_ge_zero'][label]:
            mon=term['monomial'];a=Q(term['coefficient'])
            if not mon:rhs+=a
            else:
                idx=mon[0] if len(mon)==1 else PAIR_INDEX[tuple(mon)]
                co[idx]=co.get(idx,Q(0))-a
        rows.append((co,rhs))
    for nn,(i,j)in enumerate(PAIRS):
        y=NV+nn;li,ui=boxes[i].lo,boxes[i].hi;lj,uj=boxes[j].lo,boxes[j].hi
        for ai,aj,ay,bb in ((lj,li,-1,li*lj),(uj,ui,-1,ui*uj),(-uj,-li,1,-li*uj),(-lj,-ui,1,-ui*lj)):
            co={}
            for idx,a in ((i,ai),(j,aj),(y,Q(ay))):co[idx]=co.get(idx,Q(0))+a
            rows.append((co,bb))
    return rows,boxes

def margin(aux,record):
    if record.get('kind')not in('C','H'):raise ValueError('unknown certificate')
    weights=record.get('weights')
    if not isinstance(weights,list)or not weights:raise ValueError('empty weights')
    rows,boxes=rows_and_bounds(aux);co=[Q(0)]*N;rhs=Q(0);seen=set()
    for pair in weights:
        if not isinstance(pair,list)or len(pair)!=2:raise ValueError('bad support pair')
        i,w=pair
        if type(i)is not int or type(w)is not int or i<0 or i>=len(rows)or w<=0 or i in seen:raise ValueError('bad row/weight')
        seen.add(i);a,b=rows[i];rhs+=w*b
        for j,c in a.items():co[j]+=w*c
    if record['kind']=='H':
        t=record.get('objective_weight')
        if type(t)is not int or t<=0:raise ValueError('bad objective weight')
        co[FI]-=t
    value=rhs-sum(min(c*b.lo,c*b.hi)for c,b in zip(co,boxes))
    if record['kind']=='H':value-=t*ALPHA
    return value

def verify_leaf(frame_box,record):
    result=oracle(frame_box)
    if record.get('kind')=='E':
        if result['status']not in('EMPTY','SAFE'):raise ValueError('uncertified envelope/flow leaf')
        return result['status']
    if 'aux_image'not in result:raise ValueError('C/H needs canonical image; use E for direct exclusion')
    value=margin(result['aux_image'],record)
    if record['kind']=='C' and value>=0:raise ValueError('not a strict contradiction')
    if record['kind']=='H' and value>0:raise ValueError('not an alpha upper bound')
    return 'EMPTY' if record['kind']=='C'else 'SAFE'

def propose(frame_box, *, height=True):
    """Numerical proposal only; every returned certificate is checked exactly."""
    result=oracle(frame_box)
    if result['status']in('EMPTY','SAFE'):return {'kind':'E'}
    import numpy as np
    from scipy.optimize import linprog
    rows,boxes=rows_and_bounds(result['aux_image'])
    center=np.array([float((b.lo+b.hi)/2)for b in boxes]);half=np.array([float((b.hi-b.lo)/2)for b in boxes])
    mat=np.zeros((len(rows),N));rhs=np.zeros(len(rows))
    for i,(a,b)in enumerate(rows):
        rhs[i]=float(b)
        for j,c in a.items():mat[i,j]=float(c)
    bb=rhs-mat@center;aa=mat*half
    normal=np.maximum(1e-9,np.maximum(np.abs(bb),np.max(np.abs(aa),axis=1)))
    aa/=normal[:,None];bb/=normal
    phase=np.column_stack([aa,-np.ones(len(rows))]);obj=np.zeros(N+1);obj[-1]=1
    res=linprog(obj,A_ub=phase,b_ub=bb,bounds=[(-1,1)]*N+[(0,None)],method='highs',options={'time_limit':10})
    def rationalize(lambdas,kind):
        if not np.all(np.isfinite(lambdas)):return None
        for scale in (10**6,10**9,10**12):
            ww=[max(0,int(round(float(v)*scale)))for v in lambdas]
            rec={'kind':kind,'weights':[[i,w]for i,w in enumerate(ww)if w]}
            if kind=='H':rec['objective_weight']=scale
            if not rec['weights']:continue
            try:verify_leaf(frame_box,rec);return rec
            except (ValueError,ZeroDivisionError):pass
        return None
    if res.success and res.fun>1e-10:
        cert=rationalize(-res.ineqlin.marginals/normal,'C')
        if cert:return cert
    if height:
        obj=np.zeros(N);obj[FI]=-half[FI]
        r=linprog(obj,A_ub=aa,b_ub=bb,bounds=[(-1,1)]*N,method='highs',options={'time_limit':10})
        if r.success:
            cert=rationalize(-r.ineqlin.marginals/normal,'H')
            if cert:return cert
    return None
