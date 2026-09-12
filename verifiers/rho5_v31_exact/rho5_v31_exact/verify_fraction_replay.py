#!/usr/bin/env python3
"""Independent Fraction checks on deterministic leaves; not a substitute for full replay."""
from __future__ import annotations
import json,sys,random
from pathlib import Path
from fractions import Fraction as Q
ROOT=Path(__file__).resolve().parent


def check_leaf(data,low,high,weights):
    nv=len(data['variables']);pairs=data['pairs'];n=nv+len(pairs);rows=data['rows']
    co=[Q(0)]*n;rhs=Q(0)
    for index,weight in weights:
        if weight<=0:raise ValueError('nonpositive weight')
        if index<len(rows):
            row=rows[index];rhs+=weight*row['rhs']
            for j,t in enumerate(row['coefficients']):co[j]+=weight*t
        else:
            off,typ=divmod(index-len(rows),4);i,j=pairs[off];yy=nv+off
            li,ui,lj,uj=low[i],high[i],low[j],high[j]
            ci,cj,cy,rr=[(lj,li,-1,li*lj),(uj,ui,-1,ui*uj),
                         (-uj,-li,1,-li*uj),(-lj,-ui,1,-ui*lj)][typ]
            co[i]+=weight*ci;co[j]+=weight*cj;co[yy]+=weight*cy;rhs+=weight*rr
    ll=list(low);hh=list(high)
    for i,j in pairs:
        prod=[low[i]*low[j],low[i]*high[j],high[i]*low[j],high[i]*high[j]]
        ll.append(min(prod));hh.append(max(prod))
    margin=rhs-sum(min(a*l,a*h) for a,l,h in zip(co,ll,hh))
    if margin>=0:raise AssertionError('Independent rational contradiction did not pass')
    return margin


def main(tree):
    data=json.loads((ROOT/'mc_exact_model.json').read_text());stats=json.loads((ROOT/'proof_statistics.json').read_text())
    low=[Q(n,data['root_denominator']) for n in data['root_numerators'][0]]
    high=[Q(n,data['root_denominator']) for n in data['root_numerators'][1]]
    rng=random.Random(310907)
    selected={0,1,stats['leaves']-1}|set(rng.sample(range(2,stats['leaves']-1),61))
    stack=[(low,high,0)];leaves=0;nodes=0;checked=[]
    with open(tree,encoding='ascii') as f:
        while stack:
            lo,hi,depth=stack.pop();parts=f.readline().split();nodes+=1
            if not parts:raise AssertionError('Truncated tree')
            if parts[0]=='S':
                if len(parts)!=2:raise AssertionError('Split grammar')
                j=int(parts[1]);m=(lo[j]+hi[j])/2
                ll=lo.copy();hh=hi.copy();ll[j]=m;hh[j]=m
                stack.extend([(ll,hi,depth+1),(lo,hh,depth+1)])
            elif parts[0]=='C':
                count=int(parts[1]);values=list(map(int,parts[2:]))
                if len(values)!=2*count:raise AssertionError('Leaf grammar')
                if leaves in selected:
                    weights=list(zip(values[::2],values[1::2]));margin=check_leaf(data,lo,hi,weights)
                    checked.append(dict(leaf=leaves,depth=depth,support=count,margin=str(margin)))
                leaves+=1
            else:raise AssertionError('Unpaid instruction')
        if f.read().strip():raise AssertionError('Unvisited tail')
    if nodes!=stats['nodes'] or leaves!=stats['leaves'] or len(checked)!=64:raise AssertionError('Independent counts')
    print(json.dumps(dict(status='V31_INDEPENDENT_FRACTION_CROSSCHECK_PASS',whole_partition_nodes=nodes,
                          independently_checked_leaves=len(checked),all_margins_strictly_negative=True)))
if __name__=='__main__':main(sys.argv[1])
