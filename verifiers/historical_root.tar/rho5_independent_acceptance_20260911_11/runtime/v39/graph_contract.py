"""Division-safe, exact outward interval contraction of one canonical chart.
Every exclusion refers to an exact guarded chart of the SAME maximum image.
Round48's frozen parent enclosure is rebuilt, not read from a SAFE string.
"""
from __future__ import annotations
from fractions import Fraction as Q
from functools import lru_cache
import paths
from interval_capacity import I,oracle as old_oracle,imax,imin,GAMMA,ALPHA
from high_value_contraction import oracle_from_base,contract as high_contract
from prefix_graph import *

GRID=2**36
BASE_POLYS=[(name,{tuple(t['monomial']):Q(t['coefficient'])for t in terms})for name,terms in BASE['rows_ge_zero'].items()]
PREFIX_BASE=[(n,p)for n,p in BASE_POLYS if n in ['head+','head-']or (len(n)>=2 and n[0]in'LP' and n[1].isdigit())]

class Empty(Exception):pass

def parent_enclosure(frame_box):
 return oracle_from_base(old_oracle(frame_box,local_ports=False),local_ports=False)

def floorq(q):q=Q(q);return Q((q*GRID).numerator//(q*GRID).denominator,GRID)
def ceilq(q):return -floorq(-Q(q))

def meet(b,i,lo=None,hi=None):
 old=b[i];l=old.lo if lo is None else max(old.lo,floorq(lo));u=old.hi if hi is None else min(old.hi,ceilq(hi))
 if l>u:raise Empty('coordinate_'+NAMES[i])
 b[i]=I(l,u)

@lru_cache(None)
def decomposition(terms):
 p=dict(terms);out=[]
 for i in sorted({i for m in p for i in m}):
  if any(m.count(i)>1 for m in p):continue
  a={};rest={}
  for m,c in p.items():
   if i in m:
    mm=list(m);mm.remove(i);mm=tuple(mm);a[mm]=a.get(mm,Q(0))+c
   else:rest[m]=c
  out.append((i,a,rest))
 return out

def propagate(b,rows):
 for name,p in rows:
  if interval(p,b).hi<0:raise Empty('row_'+name)
  for i,a,rest in decomposition(tuple(sorted(p.items()))):
   aa=interval(a,b)
   if aa.lo>0 or aa.hi<0:
    bb=interval(rest,b);bd=(-bb)/aa
    if aa.lo>0:meet(b,i,lo=bd.lo)
    else:meet(b,i,hi=bd.hi)

def strict_impossible(label,b):
 bl,pl=label.split('|');parts=pl.split(':')
 if bl!='B1':
  sign=1 if bl[2]=='+'else-1
  if (sign*b[17+int(bl[1])]).hi<=0:return 'strict_nonzero_upper_beta_slope'
 i=parts[1];a,bb=row_coeff(i)
 if interval(bb,b).hi<=0:return 'strict_positive_lower_prefix_slope'
 if interval(a,b).hi<=0:return 'strict_positive_lower_prefix_a'
 if parts[0]=='N':
  if b[9].lo>=1:return 'pair_requires_e_lt_one'
  aj,_=row_coeff(parts[2])
  if interval(aj,b).hi<=0:return 'strict_positive_upper_prefix_a'
 return None

def reconstruct_tail(b):
 # Intersections enclose the canonical maximum of this same restricted frame.
 k,A,B,c,d,p=b[0],b[4],b[5],b[6],b[7],b[8]
 u,x,v,q=[b[i:i+3]for i in(11,14,17,20)]
 lows={};ups={}
 for i in(1,2):
  for j in(1,2):
   xx=x[i]*q[j];yy=u[i]*v[j]
   lows[i,j]=imax(-k,-p-xx,-1-xx-yy)
   ups[i,j]=imin(k,p-xx,1-xx-yy)
   if lows[i,j].lo>ups[i,j].hi:raise Empty('tail_cell')
 R=imin(ups[1,1]-c*A,d*B-lows[2,2])
 meet(b,1,R.lo,R.hi)
 su=ups[1,2]-c*B;tu=ups[2,1]-d*A
 S=imin(b[1],su);T=imin(b[1],tu)
 meet(b,2,max(Q(0),(lows[1,2]-c*B).lo,S.lo),S.hi)
 meet(b,3,max(Q(0),(lows[2,1]-d*A).lo,T.lo),T.hi)


def direct_bounds(b,label):
 bl,pl=label.split('|');parts=pl.split(':');ai,bi=row_coeff(parts[1]);a=interval(ai,b);u=interval(bi,b)
 if bl=='B1':meet(b,10,1,1)
 else:
  eps=1 if bl[2]=='+'else-1;j=int(bl[1]);vj=eps*b[17+j];qj=eps*b[20+j]
  if vj.lo>0:
   bb=(1-qj)/vj;meet(b,10,bb.lo,bb.hi)
 if parts[0]=='E':
  meet(b,9,1,1)
  if a.lo>0:
   p=(1+u)/a;meet(b,8,p.lo,p.hi)
 else:
  aj,bj=row_coeff(parts[2]);aa=interval(aj,b);uu=interval(bj,b)
  det=aa*u-a*uu
  if det.lo>0:
   p=(u-uu)/det;e=(a-aa)/det
   meet(b,8,p.lo,p.hi);meet(b,9,e.lo,e.hi)


def contract_chart(parent,label,rounds=4):
 if label not in CHARTS:raise ValueError('unknown graph label')
 if parent.get('status')=='EMPTY':return {'status':'EMPTY','reason':'parent_empty'}
 if 'aux_image'not in parent:raise ValueError('canonical image missing')
 b=[I(*v)for v in parent['aux_image']];extra,_=CHARTS[label]
 try:
  for iteration in range(rounds):
   old=[v.data()for v in b]
   no=strict_impossible(label,b)
   if no:raise Empty(no)
   propagate(b,extra+PREFIX_BASE)
   direct_bounds(b,label)
   reconstruct_tail(b)
   hc=high_contract(b,rounds=2)
   if hc['status']=='EMPTY':raise Empty(hc['reason'])
   for i,v in enumerate(hc['aux_image']):meet(b,i,Q(v[0]),Q(v[1]))
   for name,p in BASE_POLYS:
    if interval(p,b).hi<0:raise Empty('base_interval_'+name)
   if old==[v.data()for v in b]:break
  no=strict_impossible(label,b)
  if no:raise Empty(no)
  return {'status':'BOUNDED','aux_image':[v.data()for v in b],'rounds':iteration+1}
 except Empty as err:return {'status':'EMPTY','reason':str(err)}

def closed_rows(extra):
 """Translate chart polynomial >=0 to LP rows a*z<=rhs. No new products."""
 out=[]
 for label,p in extra:
  co={};rhs=Q(0)
  for mon,c in p.items():
   if not mon:rhs+=c
   else:
    i=mon[0] if len(mon)==1 else PAIR_INDEX[mon]
    co[i]=co.get(i,Q(0))-c
  out.append((co,rhs))
 return out
