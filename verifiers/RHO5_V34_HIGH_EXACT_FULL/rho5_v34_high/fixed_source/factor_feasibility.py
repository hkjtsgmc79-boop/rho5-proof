#!/usr/bin/env python3
"""Exact bounded rank-one factor feasibility, including zero and sign boundaries.
Only rational arithmetic; SAT returns actual rational factors. UNSAT returns
one exact cycle or immediate sign/zero obstruction for EVERY forced sign mask.
This solves one isolated factor packet, not the whole RHO5 coupled source.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from typing import Sequence

@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q
    def __post_init__(self):
        if isinstance(self.lo,(float,bool)) or isinstance(self.hi,(float,bool)):
            raise TypeError('Use rational strings, integers or Fraction, not float/bool')
        object.__setattr__(self,'lo',Q(self.lo));object.__setattr__(self,'hi',Q(self.hi))
        if self.lo>self.hi:raise ValueError('empty input interval')
    def haszero(self):return self.lo<=0<=self.hi
    def contains(self,x):return self.lo<=x<=self.hi
    def times(self,other):
        p=[a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return Interval(min(p),max(p))
    def json(self):return [str(self.lo),str(self.hi)]

def magnitude(I:Interval,sgn:int):
    if sgn not in (-1,1):raise ValueError('bad sign')
    l,h=(I.lo,I.hi) if sgn==1 else (-I.hi,-I.lo)
    l=max(Q(0),l)
    if h<=0 or l>h:return None
    return (l,h)

# Edge (u,v,w,label) means exp(t_v) <= w*exp(t_u), with w>0.
def positive_problem(left,right,cells):
    m,n=len(left),len(right);edges=[]
    def add(u,v,w,label):
        w=Q(w)
        if w<=0:raise ValueError('edge weight is not positive')
        edges.append((u,v,w,label))
    for i,(l,h) in enumerate(left):
        if h is None:raise ValueError('finite upper bounds required')
        add(0,1+i,h,f'a{i}_upper')
        if l>0:add(1+i,0,1/l,f'a{i}_lower')
    for j,(l,h) in enumerate(right):
        add(1+m+j,0,h,f'b{j}_upper')
        if l>0:add(0,1+m+j,1/l,f'b{j}_lower')
    for i in range(m):
        for j in range(n):
            l,h=cells[i][j]
            add(1+m+j,1+i,h,f'z{i}{j}_upper')
            if l>0:add(1+i,1+m+j,1/l,f'z{i}{j}_lower')
    N=m+n+1;dist=[Q(1)]*N;pred=[None]*N;updated=None
    for _ in range(N):
        updated=None
        for e,(u,v,w,label) in enumerate(edges):
            cand=dist[u]*w
            if dist[v]>cand:
                dist[v]=cand;pred[v]=e;updated=v
        if updated is None:
            a=[dist[1+i]/dist[0] for i in range(m)]
            b=[dist[0]/dist[1+m+j] for j in range(n)]
            return {'status':'SAT','left':a,'right':b},edges
    v=updated
    for _ in range(N):
        if pred[v] is None:raise AssertionError('broken predecessor')
        v=edges[pred[v]][0]
    start=v;cycle=[]
    while True:
        e=pred[v];cycle.append(e);v=edges[e][0]
        if v==start:break
        if len(cycle)>N:raise AssertionError('non-simple extracted cycle')
    cycle.reverse();weight=Q(1)
    for e in cycle:weight*=edges[e][2]
    if weight>=1:raise AssertionError('cycle does not contradict feasibility')
    return {'status':'UNSAT','cycle':cycle,'product':str(weight)},edges

def forced_indices(left,right,cells):
    il=[i for i,I in enumerate(left) if not I.haszero() or any(not C.haszero() for C in cells[i])]
    jr=[j for j,I in enumerate(right) if not I.haszero() or any(not cells[i][j].haszero() for i in range(len(left)))]
    return il,jr

def branch_problem(left,right,cells,il,jr,mask):
    m=len(il);n=len(jr);signs=[1 if (mask>>i)&1 else -1 for i in range(m+n)]
    lpos=[];rpos=[];cpos=[]
    for a,i in enumerate(il):
        z=magnitude(left[i],signs[a])
        if z is None:return None,{'kind':'factor_sign','side':'left','index':i}
        lpos.append(z)
    for b,j in enumerate(jr):
        z=magnitude(right[j],signs[m+b])
        if z is None:return None,{'kind':'factor_sign','side':'right','index':j}
        rpos.append(z)
    for a,i in enumerate(il):
        row=[]
        for b,j in enumerate(jr):
            z=magnitude(cells[i][j],signs[a]*signs[m+b])
            if z is None:return None,{'kind':'product_sign','index':[i,j]}
            row.append(z)
        cpos.append(row)
    return (lpos,rpos,cpos,signs),None

def solve(left:Sequence[Interval],right:Sequence[Interval],cells:Sequence[Sequence[Interval]]):
    left=list(left);right=list(right);cells=[list(r) for r in cells]
    if len(cells)!=len(left) or any(len(r)!=len(right) for r in cells):raise ValueError('shape mismatch')
    il,jr=forced_indices(left,right,cells);N=len(il)+len(jr)
    if N>16:raise ValueError('this implementation limits forced signs to 16')
    evidence=[]
    for mask in range(1<<N):
        problem,bad=branch_problem(left,right,cells,il,jr,mask)
        if bad:
            evidence.append({'mask':mask,**bad});continue
        lp,rp,cp,signs=problem
        ans,edges=positive_problem(lp,rp,cp)
        if ans['status']=='SAT':
            a=[Q(0)]*len(left);b=[Q(0)]*len(right)
            for t,i in enumerate(il):a[i]=signs[t]*ans['left'][t]
            for t,j in enumerate(jr):b[j]=signs[len(il)+t]*ans['right'][t]
            if not check_witness(left,right,cells,a,b):raise AssertionError('invalid reconstructed factors')
            return {'status':'SAT','left':list(map(str,a)),'right':list(map(str,b)),'forced_left':il,'forced_right':jr}
        evidence.append({'mask':mask,'kind':'negative_cycle','cycle':ans['cycle'],'product':ans['product']})
    return {'status':'UNSAT','forced_left':il,'forced_right':jr,'branches':evidence}

def check_witness(left,right,cells,a,b):
    a=list(map(Q,a));b=list(map(Q,b))
    return (len(a)==len(left) and len(b)==len(right)
        and all(I.contains(x) for I,x in zip(left,a)) and all(I.contains(x) for I,x in zip(right,b))
        and all(cells[i][j].contains(a[i]*b[j]) for i in range(len(a)) for j in range(len(b))))

def verify(left,right,cells,cert):
    if cert['status']=='SAT':
        if not check_witness(left,right,cells,cert['left'],cert['right']):raise ValueError('bad SAT witness')
        return True
    if cert['status']!='UNSAT':raise ValueError('unknown status')
    il,jr=forced_indices(left,right,cells);N=len(il)+len(jr)
    if cert['forced_left']!=il or cert['forced_right']!=jr:raise ValueError('forced-variable mismatch')
    branches=cert['branches']
    if len(branches)!=1<<N:raise ValueError('missing sign branches')
    for mask,record in enumerate(branches):
        if record['mask']!=mask:raise ValueError('duplicate or missing sign mask')
        problem,bad=branch_problem(left,right,cells,il,jr,mask)
        if bad:
            if record!={'mask':mask,**bad}:raise ValueError('wrong immediate obstruction')
            continue
        if record['kind']!='negative_cycle':raise ValueError('missing actual cycle')
        lp,rp,cp,signs=problem
        # Independently build the edge dictionary; do not rerun the solver.
        m,n=len(lp),len(rp);edges=[]
        def add(u,v,w):edges.append((u,v,Q(w)))
        for i,(l,h) in enumerate(lp):
            add(0,i+1,h)
            if l>0:add(i+1,0,1/l)
        for j,(l,h) in enumerate(rp):
            add(m+j+1,0,h)
            if l>0:add(0,m+j+1,1/l)
        for i in range(m):
            for j in range(n):
                l,h=cp[i][j];add(m+j+1,i+1,h)
                if l>0:add(i+1,m+j+1,1/l)
        cycle=record['cycle']
        if not cycle or any(type(e)!=int or not 0<=e<len(edges) for e in cycle):raise ValueError('bad edge index')
        product=Q(1)
        for t,e in enumerate(cycle):
            u,v,w=edges[e];next_u=edges[cycle[(t+1)%len(cycle)]][0]
            if v!=next_u:raise ValueError('edges do not form a closed directed cycle')
            product*=w
        if product>=1 or str(product)!=record['product']:raise ValueError('cycle is not strictly negative')
    return True
