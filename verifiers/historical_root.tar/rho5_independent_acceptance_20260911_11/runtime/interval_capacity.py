#!/usr/bin/env python3
"""Exact outer enclosure of the six-variable canonical reconstruction.
Only the 17 frame variables are branched. An EMPTY result excludes complete
sources of height >= gamma; a SAFE result proves alpha for those sources.
Unresolved sign/zero charts fall back to wider intervals, never to exclusion.
"""
from __future__ import annotations
from fractions import Fraction as Q
from dataclasses import dataclass
from pathlib import Path
import json
from capacity import FRAME_NAMES, GAP_NAMES, rational, encode

ROOT=Path(__file__).parent
GAMMA=Q(4132517,1000000)
ALPHA=Q(json.loads((ROOT/'dependency/alpha.json').read_text())['isolating_interval']['lower'])
CERT=json.loads((ROOT/'dependency/two_gap_certificate.json').read_text())
if CERT['coordinate_order']!=list(GAP_NAMES):
    raise ValueError('Frozen local-flow coordinate order mismatch')
CENTERS=[list(map(Q,c['center']))for c in CERT['cases']]
@dataclass(frozen=True)
class I:
    lo: Q
    hi: Q
    def __init__(self,lo,hi=None):
        lo=rational(lo);hi=lo if hi is None else rational(hi)
        if lo>hi:raise ValueError('reversed interval')
        object.__setattr__(self,'lo',lo);object.__setattr__(self,'hi',hi)
    def __add__(self,o):
        o=asI(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-asI(o)
    def __rsub__(self,o):return asI(o)+-self
    def __mul__(self,o):
        o=asI(o);v=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi];return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=asI(o)
        if o.lo<=0<=o.hi:raise ZeroDivisionError('interval divisor contains zero')
        return self*I(1/o.hi,1/o.lo)
    def __rtruediv__(self,o):return asI(o)/self
    def abs(self):
        if self.lo>=0:return self
        if self.hi<=0:return -self
        return I(0,max(-self.lo,self.hi))
    def intersects(self,o):o=asI(o);return self.lo<=o.hi and o.lo<=self.hi
    def intersection(self,o):
        o=asI(o)
        if not self.intersects(o):return None
        return I(max(self.lo,o.lo),min(self.hi,o.hi))
    def data(self):return [str(self.lo),str(self.hi)]

def asI(o):return o if isinstance(o,I)else I(o)
def imin(*args):return I(min(asI(v).lo for v in args),min(asI(v).hi for v in args))
def imax(*args):return I(max(asI(v).lo for v in args),max(asI(v).hi for v in args))
def wide_beta(v,q):
    lows=[I(0)];ups=[I(1)];complete=True
    for vi,qi in zip(v,q):
        if vi.lo>0:
            lows.append((-1-qi)/vi);ups.append((1-qi)/vi)
        elif vi.hi<0:
            lows.append((1-qi)/vi);ups.append((-1-qi)/vi)
        elif vi.lo==vi.hi==0:
            if not qi.intersects(I(-1,1)):return None
        else:
            complete=False
            if not (qi+I(0,1)*vi).intersects(I(-1,1)):return None
    blo=imax(*lows);bhi=imin(*ups)
    if blo.lo>bhi.hi or bhi.hi<0:return None
    return I(max(Q(0),bhi.lo)if complete else Q(0), min(Q(1),bhi.hi))

def wide_prefix(u,x,beta):
    """P exact cap list when all relevant signs are resolved; safe bound otherwise."""
    rows=[('head',I(1),beta)];complete=beta.lo>0
    upper_candidates=[I(1)+beta]
    for j,(ui,xi)in enumerate(zip(u,x)):
        if xi.lo==xi.hi==0:continue
        if xi.lo>0:a,b=xi,ui
        elif xi.hi<0:a,b=-xi,-ui
        else:complete=False;continue
        rows.append((f'L{j}',a,b))
        upper_candidates.append((1+imax(I(0),b))/a)
        if not(b.lo>0 or b.hi<0 or b.lo==b.hi==0):complete=False
    caps=[]
    for _,a,b in rows:
        if b.lo>=0:caps.append((1+b)/a)
    for _,ai,bi in rows:
        if bi.lo<=0:continue
        for _,aj,bj in rows:
            if bj.hi>=0:continue
            caps.append((bi-bj)/(aj*bi-ai*bj))
    upper_candidates+=caps
    pu=min(Q(2),min(z.hi for z in upper_candidates))
    if pu<1:return None
    if complete:
        p=imin(*caps).intersection(I(1,2))
        if p is None:return None
        es=[I(0)]+[(a*p-1)/b for _,a,b in rows if b.lo>0]
        e=imax(*es).intersection(I(0,1))
        if e is None:return None
    else:p=I(1,pu);e=I(0,1)
    return p,e,complete

def root_box():
    bounds=[(4*GAMMA/9,Q(9,4)),(Q(-9,4),0),(Q(-9,4),Q(9,4)),(-1,1),(-1,1)]
    bounds += [(-1,1)]*9 +[(-2,2)]*3
    bounds[8]=(0,1) # x0
    return [I(*z)for z in bounds]

def oracle(box, *, local_ports=True):
    if len(box)!=17:raise ValueError('17 frame intervals required')
    b=[v if isinstance(v,I) else I(*v) for v in box]
    if any(v.lo<r.lo or v.hi>r.hi for v,r in zip(b,root_box())):
        raise ValueError('Oracle boxes must be subsets of the frozen B17 root')
    k,A,B,c,d=b[:5];u,x,v,q=[b[a:a+3]for a in (5,8,11,14)]
    def no(why):return {'status':'EMPTY','reason':why}
    if k.lo<=0:raise ValueError('strict positive k lower bound required')
    for y in u+x+v:
        if not y.intersects(I(-1,1)):return no('receiver_box')
    beta=wide_beta(v,q)
    if beta is None:return no('beta_interval')
    pre=wide_prefix(u,x,beta)
    if pre is None:return no('prefix_capacity')
    p,e,charts=pre
    # These are necessary for any complete height>=gamma canonical source.
    p=p.intersection(I(GAMMA/4,min(Q(2),4/k.lo)))
    if p is None:return no('prefix_low_order_bound')
    for qi in q:
        if (p-qi).hi<0 or(p+qi).hi<0:return no('q_stage')
    fixed={(0,0):k,(0,1):A,(0,2):B,(1,0):c*k,(2,0):d*k}
    for (i,j),z in fixed.items():
        if(k-z).hi<0 or(k+z).hi<0:return no(f'D{i}{j}')
        ss=z+x[i]*q[j];oo=ss+u[i]*v[j]
        if(p-ss).hi<0 or(p+ss).hi<0:return no(f'S{i}{j}')
        if(1-oo).hi<0 or(1+oo).hi<0:return no(f'O{i}{j}')
    lo={};up={}
    for i in (1,2):
        for j in (1,2):
            xx=x[i]*q[j];yy=u[i]*v[j]
            lo[i,j]=imax(-k,-p-xx,-1-xx-yy)
            up[i,j]=imin(k,p-xx,1-xx-yy)
            if lo[i,j].lo>up[i,j].hi:return no(f'cell_{i}{j}')
    ca,cb,da,db=c*A,c*B,d*A,d*B
    rl=imax(I(0),lo[1,1]-ca,db-up[2,2]);R=imin(up[1,1]-ca,db-lo[2,2])
    sl=imax(I(0),lo[1,2]-cb);su=up[1,2]-cb
    tl=imax(I(0),lo[2,1]-da);tu=up[2,1]-da
    R=R.intersection(I(GAMMA/2,min(Q(4),2*k.hi)))
    if R is None or R.hi<rl.lo:return no('r_capacity')
    R=I(max(R.lo,rl.lo),R.hi)
    S=imin(R,su).intersection(I(max(Q(0),sl.lo),R.hi)) if max(Q(0),sl.lo)<=R.hi else None
    T=imin(R,tu).intersection(I(max(Q(0),tl.lo),R.hi)) if max(Q(0),tl.lo)<=R.hi else None
    if S is None or T is None:return no('arm_capacity')
    sig=imax(I(0),R-su).intersection(I(0,R.hi));tau=imax(I(0),R-tu).intersection(I(0,R.hi))
    if sig is None or tau is None:return no('gap_capacity')
    # Monotonicity holds on 0<=s,t<=r. All intervals are enclosing, not samples.
    ub=min(R.hi+S.hi*T.hi/R.hi, Q(9,4)*k.hi,4*p.hi)
    if ub<GAMMA:return no('height_below_trigger')
    gap=[k,R,-R,A,B,c,d,p,e,beta]+u+x+v+q+[sig,tau]
    aux=[k,R,S,T,A,B,c,d,p,e,beta]+u+x+v+q+[I(GAMMA,ub)]
    result={'status':'OPEN','height_upper':str(ub),'complete_prefix_charts':charts,
            'gap_image':[z.data()for z in gap],'aux_image':[z.data()for z in aux]}
    if ub<=ALPHA:return {**result,'status':'SAFE','port':'height'}
    if local_ports:
        for j,center in enumerate(CENTERS):
            dist=max(max(abs(z.lo-cc),abs(z.hi-cc))for z,cc in zip(gap,center))
            budget=dist+3*(sig.hi+tau.hi)
            if budget<Q(1,1250):
                return {**result,'status':'SAFE','port':f'canonical_flow_{j}', 'budget':str(budget),
                        'gain_lower':str((sig.lo+tau.lo)/10)}
    return result

if __name__=='__main__':
    import argparse
    a=argparse.ArgumentParser();a.add_argument('box');a=a.parse_args()
    box=json.loads(Path(a.box).read_text())
    print(json.dumps(oracle(box),ensure_ascii=False,indent=2))
