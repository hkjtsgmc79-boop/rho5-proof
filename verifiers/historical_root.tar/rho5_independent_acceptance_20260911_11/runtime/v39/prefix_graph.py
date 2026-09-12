#!/usr/bin/env python3
"""V39: exact guarded canonical-prefix graph, and a closed outer cover.
The accepted closed charts are supersets, not exact maximizer graphs at zero
slopes. All 189 labels must be covered. No B18 tail contacts are added.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
import json
import paths
from interval_capacity import I
from relaxation import BASE,NAMES,PAIRS,PAIR_INDEX,N,NV
from capacity import rational,prefix_capacity,beta_interval

# A polynomial is a dictionary (tuple of actual coordinate indices)->Fraction.
def poly(c=0):return {():Q(c)} if c else {}
def var(name):return {(NAMES.index(name),):Q(1)}
def add(*ps):
 d={}
 for p in ps:
  for m,c in p.items():d[m]=d.get(m,Q(0))+c
 return {m:c for m,c in d.items() if c}
def scale(p,c):return {m:Q(c)*a for m,a in p.items() if Q(c)*a}
def sub(p,q):return add(p,scale(q,-1))
def mul(p,q):
 d={}
 for m,c in p.items():
  for n,a in q.items():
   z=tuple(sorted(m+n));d[z]=d.get(z,Q(0))+c*a
 return {m:c for m,c in d.items()if c}
def ge_row(p,label):return (label,p)
def eval_point(p,z):
 out=Q(0)
 for m,c in p.items():
  for i in m:c*=z[i]
  out+=c
 return out
def interval(p,b):
 out=I(0)
 for m,c in p.items():
  t=I(c)
  for i in m:t=t*b[i]
  out=out+t
 return out

def row_coeff(label):
 if label=='H':return poly(1),var('beta')
 j=int(label[1]);sgn=1 if label[2]=='+' else -1
 return scale(var('x'+str(j)),sgn),scale(var('u'+str(j)),sgn)

def original_slack(label):
 a,b=row_coeff(label)
 return add(poly(1),scale(mul(a,var('p')),-1),mul(b,var('e')))

# x0>=0 is the frozen B17 normalization. L0- cannot provide the
# required positive objective slope at a high canonical prefix.
ROW_LABELS=('H','L0+','L1+','L1-','L2+','L2-')
BETA_LABELS=('B1',)+tuple(f'B{j}{s}'for j in range(3)for s in ('+','-'))
PREFIX_LABELS=tuple([f'E:{i}'for i in ROW_LABELS]+[
 f'N:{i}:{j}'for i in ROW_LABELS for j in ROW_LABELS
 if i!=j and j!='H' and (i=='H' or i[1]!=j[1])])
assert len(PREFIX_LABELS)==27
GRAPH_LABELS=tuple(f'{b}|{p}'for b,p in product(BETA_LABELS,PREFIX_LABELS))
assert len(GRAPH_LABELS)==189

def chart(label):
 if label not in GRAPH_LABELS:raise ValueError('Unknown canonical-prefix chart')
 bl,pl=label.split('|');rows=[];equalities=[]
 def eq(p,l):
  equalities.append((l,p));rows.extend([(l+'+',p),(l+'-',scale(p,-1))])
 def ge(p,l):rows.append((l,p))
 if bl=='B1':eq(sub(poly(1),var('beta')),'beta_one')
 else:
  j=int(bl[1]);sgn=1 if bl[2]=='+'else -1
  vv=scale(var(f'v{j}'),sgn);qq=scale(var(f'q{j}'),sgn)
  eq(add(poly(1),scale(qq,-1),scale(mul(var('beta'),vv),-1)),'beta_contact')
  ge(vv,'beta_direction');ge(qq,'q_same_direction');ge(sub(poly(1),qq),'q_le_one')
 parts=pl.split(':');i=parts[1];a,b=row_coeff(i)
 # Closed versions of the exact positive-slope guard. a>=1/2 follows
 # from a*p=1+b*e, p<=2. The strict b>0 belongs only to the exact graph.
 ge(b,'lower_b_nonnegative');ge(sub(scale(a,2),poly(1)),'lower_a_ge_half')
 eq(original_slack(i),'lower_contact')
 if parts[0]=='E':eq(sub(poly(1),var('e')),'e_one')
 else:
  j=parts[2];aj,bj=row_coeff(j)
  ge(scale(bj,-1),'upper_b_nonpositive');ge(aj,'upper_a_nonnegative')
  ge(sub(a,aj),'ordered_a')
  eq(original_slack(j),'upper_contact')
 for _,p in rows:
  for m in p:
   if len(m)>2:raise AssertionError('Not quadratic')
   if len(m)==2 and m not in PAIR_INDEX:raise AssertionError(('New product',m))
 return rows,equalities

CHARTS={s:chart(s)for s in GRAPH_LABELS}

def exact_labels(u,x,v,q,beta,p,e):
 """Labels of the exact guarded graph at a feasible triple (rational)."""
 u,x,v,q=[[rational(t)for t in arr]for arr in(u,x,v,q)]
 beta,p,e=map(rational,(beta,p,e))
 if not(p>1 and 0<beta<=1 and 0<e<=1 and x[0]>=0):return []
 if any(abs(t)>1 for t in u+x+v):return []
 if p-e*beta>1 or any(abs(p*xi-e*ui)>1 for ui,xi in zip(u,x))or any(abs(qj+beta*vj)>1 for vj,qj in zip(v,q)):return []
 bl=[]
 if beta==1:bl.append('B1')
 for j,(vj,qj)in enumerate(zip(v,q)):
  for eps in (1,-1):
   if eps*vj>0 and eps*(qj+beta*vj)==1:bl.append(f'B{j}'+('+'if eps==1 else '-'))
 coeff={'H':(Q(1),beta)}
 for name in ROW_LABELS[1:]:
  j=int(name[1]);eps=1 if name[2]=='+'else-1
  coeff[name]=(eps*x[j],eps*u[j])
 pl=[]
 if e==1:
  for i,(ai,bi)in coeff.items():
   if ai>0 and bi>0 and ai*p-bi*e==1:pl.append('E:'+i)
 else:
  for i,(ai,bi)in coeff.items():
   if not(ai>0 and bi>0 and ai*p-bi*e==1):continue
   for j,(aj,bj)in coeff.items():
    if i==j or j=='H' or(i!='H'and i[1]==j[1]):continue
    if aj>0 and bj<=0 and aj*p-bj*e==1:pl.append(f'N:{i}:{j}')
 return [f'{a}|{b}'for a,b in product(bl,pl)]

def check_exact_prefix(u,x,v,q,beta,p,e):
 labels=exact_labels(u,x,v,q,beta,p,e)
 if not labels:return False
 bi=beta_interval(list(map(Q,v)),list(map(Q,q)))
 P,E,_=prefix_capacity(list(map(Q,u)),list(map(Q,x)),Q(beta))
 if bi is None or Q(beta)!=bi[1] or Q(p)!=P or Q(e)!=E:
  raise AssertionError('Exact guarded graph admitted a noncanonical point')
 return True

if __name__=='__main__':
 print(json.dumps({'beta_charts':len(BETA_LABELS),'oriented_prefix_charts':len(PREFIX_LABELS),'closed_charts':len(GRAPH_LABELS),'actual_shared_products_unchanged':len(PAIRS),'whole_B_closed':False},indent=2))
