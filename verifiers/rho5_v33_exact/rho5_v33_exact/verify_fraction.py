#!/usr/bin/env python3
"""Independent Python partition reconstruction and sampled Fraction leaf checks.
Full leaf acceptance is by the separate arbitrary-integer C++ verifier.
"""
from __future__ import annotations
from pathlib import Path
from fractions import Fraction as Q
import argparse,json,math
from rankone_interval import exclusion

def check_leaf(data,lo,hi,weights):
 nv=len(lo);pairs=data['pairs'];base=data['rows'];n=nv+len(pairs)
 L=[Q(t) for t in lo];U=[Q(t) for t in hi]
 for i,j in pairs:
  ends=[L[i]*L[j],L[i]*U[j],U[i]*L[j],U[i]*U[j]];L.append(min(ends));U.append(max(ends))
 C=[Q(0)]*n;B=Q(0);seen=set()
 for row,weight in weights:
  assert weight>0 and row not in seen;seen.add(row)
  if row<len(base):
   for j,c in enumerate(base[row]['coefficients']):C[j]+=weight*c
   B+=weight*base[row]['rhs']
  else:
   z,t=divmod(row-len(base),4);i,j=pairs[z];yy=nv+z
   if t==0:ci,cj,cy,bb=L[j],L[i],-1,L[i]*L[j]
   elif t==1:ci,cj,cy,bb=U[j],U[i],-1,U[i]*U[j]
   elif t==2:ci,cj,cy,bb=-U[j],-L[i],1,-L[i]*U[j]
   else:ci,cj,cy,bb=-L[j],-U[i],1,-U[i]*L[j]
   C[i]+=weight*ci;C[j]+=weight*cj;C[yy]+=weight*cy;B+=weight*bb
 margin=B-sum(c*(l if c>=0 else u) for c,l,u in zip(C,L,U))
 assert margin<0,margin
 return margin

def run(model,tree,allow_open=False):
 data=json.loads(Path(model).read_text());den=data['root_denominator'];lo,hi=[[Q(t,den) for t in z] for z in data['root_numerators']]
 stats={'nodes':0,'splits':0,'closed':0,'open':0,'fraction_rechecked':0,'max_depth':0,'rank_one_leaves':0,'rank_one_rechecked':0}
 stream=open(tree);samples=[]
 def visit(lo,hi,depth=0):
  line=stream.readline()
  if not line:raise ValueError('truncated tree')
  fields=line.split();stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
  if fields[0]=='S':
   assert len(fields)==2;i=int(fields[1]);assert 0<=i<len(lo) and lo[i]<hi[i]
   stats['splits']+=1;m=(lo[i]+hi[i])/2;lh=hi[:];lh[i]=m;hl=lo[:];hl[i]=m
   visit(lo,lh,depth+1);visit(hl,hi,depth+1)
  elif fields[0]=='O':
   assert allow_open and len(fields)==1;stats['open']+=1
  elif fields[0]=='R':
   assert len(fields)==2 and 0<=int(fields[1])<=3
   stats['closed']+=1;stats['rank_one_leaves']+=1
   idx=stats['rank_one_leaves']
   if idx<=8 or idx%997==0:
    assert exclusion(lo,hi)==int(fields[1]);stats['rank_one_rechecked']+=1
  elif fields[0]=='C':
   n=int(fields[1]);assert n>0 and len(fields)==2+2*n
   weights=list(zip(map(int,fields[2::2]),map(int,fields[3::2])))
   assert all(0<=i<len(data['rows'])+4*len(data['pairs']) and w>0 for i,w in weights)
   assert len({i for i,w in weights})==n
   idx=stats['closed'];stats['closed']+=1
   if idx<8 or idx%4093==0:
    margin=check_leaf(data,lo,hi,weights);stats['fraction_rechecked']+=1
    samples.append({'leaf':idx,'margin':str(margin)})
  else:raise ValueError('unknown or unpaid tag: '+fields[0])
 visit(lo,hi)
 if stream.read().strip():raise ValueError('unvisited tail')
 assert stats['nodes']==2*stats['splits']+1 and stats['closed']+stats['open']==stats['splits']+1
 stats['status']='INDEPENDENT_PARTITION_AND_FRACTION_SAMPLE_PASS'
 stats['scope']='All partition nodes; deterministic sample of closed leaf arithmetic. Not standalone full arithmetic replay.'
 stats['samples']=samples;return stats
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('model');ap.add_argument('tree');ap.add_argument('--allow-open',action='store_true');ap.add_argument('--output');a=ap.parse_args();r=run(a.model,a.tree,a.allow_open)
 if a.output:Path(a.output).write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps({k:v for k,v in r.items() if k!='samples'}))
