#!/usr/bin/env python3
"""Symbolic identities and independent rational boundary controls.
This finite suite checks implementation; universal coverage is proved in THEORY.
"""
from fractions import Fraction as Q
from itertools import combinations
import json,random
from pathlib import Path
import sympy as s
from prefix_graph import *
from capacity import encode

def vertex_prefix(u,x,beta):
 # Each pair (a,b,c) means a*p+b*e<=c. No absolute-value capacity formula used.
 rows=[(Q(1),-beta,Q(1)),(Q(-1),Q(0),Q(-1)),(Q(0),Q(-1),Q(0)),(Q(0),Q(1),Q(1))]
 for ui,xi in zip(u,x):rows +=[(xi,-ui,Q(1)),(-xi,ui,Q(1))]
 vertices=[]
 for a,b in combinations(rows,2):
  det=a[0]*b[1]-a[1]*b[0]
  if not det:continue
  p=(a[2]*b[1]-a[1]*b[2])/det;e=(a[0]*b[2]-a[2]*b[0])/det
  if all(A*p+B*e<=C for A,B,C in rows):vertices.append((p,e))
 if not vertices:raise AssertionError('p=1,e=0 must be feasible')
 return max(vertices,key=lambda z:(z[0],-z[1]))

def run():
 ai,aj,bi,bj,p,e,P,E,beta,Bstar,v,q,eps=s.symbols('ai aj bi bj p e P E beta Bstar v q eps')
 D=aj*bi-ai*bj;g=1-ai*p+bi*e;h=1-aj*p+bj*e
 expressions={
  'pair_p_payment': D*((bi-bj)/D-p)-(bi*h-bj*g),
  'pair_e_residual': D*(e-(ai-aj)/D)-(aj*g-ai*h),
  'endpoint_payment':ai*((1+bi)/ai-p)-(g+bi*(1-e)),
  'pair_first_contact':ai*(bi-bj)/D-bi*(ai-aj)/D-1,
  'pair_second_contact':aj*(bi-bj)/D-bj*(ai-aj)/D-1,
  'beta_payment':eps*v*((eps-q)/v-beta)-(1-eps*(q+beta*v)),
 }
 # beta identity requires eps^2=1; reduce in that polynomial ideal.
 for name,z in expressions.items():
  if name=='beta_payment':z=s.rem(s.together(z).as_numer_denom()[0],eps**2-1,eps)
  assert s.cancel(z)==0,name
 rng=random.Random(20260909);count=0;high=0;chartocc={};minimizer_checks=0
 for n in range(900):
  u=[Q(rng.randint(-10,10),10)for _ in range(3)]
  x=[Q(rng.randint(0,10),10)]+[Q(rng.randint(-10,10),10)for _ in range(2)]
  v=[Q(rng.randint(-10,10),10)for _ in range(3)]
  target=Q(rng.randint(0,10),10)
  # Guarantee at least one feasible beta by generating from actual P_j values.
  q=[Q(rng.randint(-10,10),10)-target*vv for vv in v]
  interval_beta=beta_interval(v,q);assert interval_beta is not None
  B=interval_beta[1];pp,ee,_=prefix_capacity(u,x,B)
  assert(pp,ee)==vertex_prefix(u,x,B)
  count+=1
  if pp<=1:continue
  high+=1;labels=exact_labels(u,x,v,q,B,pp,ee);assert labels
  assert check_exact_prefix(u,x,v,q,B,pp,ee)
  zz=[Q(0)]*24;zz[8:11]=[pp,ee,B];zz[11:14]=u;zz[14:17]=x;zz[17:20]=v;zz[20:23]=q
  for label in labels:
   for name,poly in CHARTS[label][0]:assert eval_point(poly,zz)>=0,(label,name)
   chartocc[label]=chartocc.get(label,0)+1
  # All feasible polygon vertices satisfying exact labels must be canonical.
  for ealt in (Q(0),Q(1),ee/2,(ee+1)/2):
   if exact_labels(u,x,v,q,B,pp,ealt):
    assert ealt==ee;minimizer_checks+=1
 controls=[]
 def control(name,u,x,v,q,expected=None):
  u,x,v,q=[[Q(z)for z in y]for y in(u,x,v,q)];ib=beta_interval(v,q)
  assert ib is not None;be=ib[1];pp,ee,_=prefix_capacity(u,x,be)
  assert(pp,ee)==vertex_prefix(u,x,be)
  labs=exact_labels(u,x,v,q,be,pp,ee)
  if pp>1:assert labs
  if expected:assert(be,pp,ee)==tuple(Q(z)for z in expected)
  controls.append(encode({'name':name,'u':u,'x':x,'v':v,'q':q,'beta':be,'p':pp,'e':ee,'exact_charts':labs}))
 control('flat_upper_zero_b',['0',0,0],['5/6',0,0],[1,0,0],['1/2',0,0],['1/2','6/5','2/5'])
 control('zero_receiver_at_saturation',[0,0,0],[0,0,0],[0,0,0],[1,-1,0],[1,2,1])
 control('single_point_beta',[0,0,0],[0,0,0],[1,1,0],['1/2','-3/2',0],['1/2','3/2',1])
 control('duplicate_parallel_rows',['1/2','1/2',0],[1,1,0],[1,0,0],['1/2',0,0],['1/2','3/2',1])
 control('negative_upper_beta_direction',[0,0,0],[0,0,0],[-1,0,0],['-1/2',0,0],['1/2','3/2',1])
 control('all_zero_x',[1,-1,0],[0,0,0],[1,0,0],['1/2',0,0],['1/2','3/2',1])
 # Counterexamples to using contact alone, and to taking closed charts as exact.
 assert not exact_labels([0,0,0],[Q(5,6),0,0],[1,0,0],[Q(1,2),0,0],Q(1,2),Q(6,5),Q(1))
 assert not exact_labels([Q(1,10),0,0],[Q(4,5),0,0],[1,0,0],[Q(1,2),0,0],Q(1,2),Q(4,3),Q(2,3))
 assert not exact_labels([0,0,0],[0,0,0],[1,0,0],[Q(-3,2),0,0],Q(1,2),Q(3,2),Q(1))
 # Max-beta graph is not closed: nonzero v tends to zero with q tending to 1.
 for n in (2,10,100,1000):
  vb=[Q(1,n),Q(0),Q(0)];qb=[1-Q(1,2*n),Q(0),Q(0)]
  assert beta_interval(vb,qb)[1]==Q(1,2)
 assert beta_interval([Q(0)]*3,[Q(1),Q(0),Q(0)])[1]==1
 out={'symbolic_identities':len(expressions),'independent_prefix_polygon_cases':count,'high_prefix_cases':high,'exact_canonical_vertex_checks':minimizer_checks,'boundary_controls':controls,'raw_contact_counterexamples':3,'nonclosed_beta_graph_sequence_checks':5,'finite_sample_not_global_proof':True,'shared_products':len(PAIRS),'beta_labels':len(BETA_LABELS),'prefix_labels':len(PREFIX_LABELS),'total_labels':len(GRAPH_LABELS)}
 return out

if __name__=='__main__':
 r=run();print(json.dumps(r,indent=2));
