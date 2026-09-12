"""V40 same-denominator homogenization of source rows on a prefix graph.
All actual coordinates retained; new monomials are unique, actual products.
Bound verification uses only rational algebra and McCormick inequalities.
"""
from itertools import combinations
from projective_graph import *

def substitute_fixed_beta(p,label):
 if label.split('|')[0]!='B1':return p
 out={}
 for m,c in p.items():
  mm=tuple(i for i in m if i!=10);out[mm]=out.get(mm,Q(0))+c
 return {m:c for m,c in out.items()if c}

@lru_cache(None)
def homogeneous_rows(label):
 den,num,en,_=projective_data(label);out=[]
 for name,g in BASE_POLYS:
  p0={};pp={};pe={}
  for m,c in g.items():
   if 8 in m:
    if m.count(8)!=1 or 9 in m:raise ValueError('source not affine in p,e')
    mm=list(m);mm.remove(8);pp[tuple(mm)]=c
   elif 9 in m:
    if m.count(9)!=1:raise ValueError('source not affine in p,e')
    mm=list(m);mm.remove(9);pe[tuple(mm)]=c
   else:p0[m]=c
  if not pp and not pe:continue
  new=add(mul(den,p0),mul(num,pp),mul(en,pe))
  new=substitute_fixed_beta(new,label)
  if new:out.append(('homogenized_'+name,new))
 return out

def contract_homogeneous(parent,label,rounds=6):
 out=contract_projective(parent,label)
 if out['status']=='EMPTY':return out
 b=[I(*x)for x in out['aux_image']];hom=homogeneous_rows(label);new=projective_data(label)[3]
 try:
  for it in range(rounds):
   prev=[x.data()for x in b]
   propagate(b,hom+new+projected_range_rows(b,label)+CHARTS[label][0]+BASE_POLYS)
   direct_bounds(b,label);reconstruct_tail(b)
   hc=high_contract(b,rounds=2)
   if hc['status']=='EMPTY':raise Empty(hc['reason'])
   for i,v in enumerate(hc['aux_image']):meet(b,i,Q(v[0]),Q(v[1]))
   no=strict_impossible(label,b)
   if no:raise Empty(no)
   if prev==[x.data()for x in b]:break
  return {'status':'BOUNDED','aux_image':[x.data()for x in b],'rounds':it+1}
 except Empty as err:return {'status':'EMPTY','reason':str(err)}


def monomial_interval(mon,boxes):
 ans=I(1)
 for i in mon:ans=ans*boxes[i]
 return ans

def generalized_rows(aux,label,selected=None):
 actual=[I(*v)for v in aux]
 hom=homogeneous_rows(label)
 if selected is not None:
  if not isinstance(selected,(list,tuple))or len(set(selected))!=len(selected):raise ValueError('Invalid homogeneous selector')
  known={name.removeprefix('homogenized_') for name,_ in hom}
  if any(type(s)is not str or s not in known for s in selected):raise ValueError('Unknown homogeneous source row')
  hom=[(n,p)for n,p in hom if n.removeprefix('homogenized_') in selected]
 polys=BASE_POLYS+CHARTS[label][0]+projective_data(label)[3]+projected_range_rows(actual,label)+hom
 # Include all divisors of each appearing monomial. Repeated monomials get
 # a single shared column, and all one-factor decompositions are checked.
 mon=set()
 for _,p in polys:
  for m in p:
   for d in range(2,len(m)+1):mon.update(tuple(m[i]for i in pick)for pick in combinations(range(len(m)),d))
 mon=sorted(mon,key=lambda m:(len(m),m));index={m:24+i for i,m in enumerate(mon)}
 boxes=actual+[monomial_interval(m,actual)for m in mon];rows=[]
 for _,p in polys:
  a={};rhs=p.get((),Q(0))
  for m,c in p.items():
   if not m:continue
   j=m[0]if len(m)==1 else index[m];a[j]=a.get(j,Q(0))-c
  rows.append((a,rhs))
 for m in mon:
  y=index[m];splits=[]
  for j in sorted(set(m)):
   rest=list(m);rest.remove(j);rest=tuple(rest);k=rest[0]if len(rest)==1 else index[rest]
   pair=tuple(sorted((j,k)))
   if pair not in splits:splits.append(pair)
  for i,k in splits:
   li,ui=boxes[i].lo,boxes[i].hi;lk,uk=boxes[k].lo,boxes[k].hi
   for ai,ak,az,bb in ((lk,li,-1,li*lk),(uk,ui,-1,ui*uk),(-uk,-li,1,-li*uk),(-lk,-ui,1,-ui*lk)):
    a={}
    for ix,c in ((i,ai),(k,ak),(y,Q(az))):a[ix]=a.get(ix,Q(0))+c
    rows.append((a,bb))
 return rows,boxes
