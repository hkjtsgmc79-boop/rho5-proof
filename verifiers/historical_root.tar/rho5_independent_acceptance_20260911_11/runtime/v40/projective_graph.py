"""V40: division-free degree-two projection of the ENTIRE prefix polytope
at a canonical active basis. Coefficient minors never mix distinct sources.
"""
from functools import lru_cache
from full_source import *
ALL_ROWS=('H','L0+','L0-','L1+','L1-','L2+','L2-')

@lru_cache(None)
def projective_data(label):
 parts=label.split('|')[1].split(':');a,b=row_coeff(parts[1]);rows=[]
 if parts[0]=='E':
  den=a;num=add(poly(1),b);en=a
  for name in ALL_ROWS:
   aa,bb=row_coeff(name)
   value=sub(mul(a,add(poly(1),bb)),mul(aa,num))
   if value:rows.append(('projection_E_'+name,value))
 else:
  aa,bb=row_coeff(parts[2]);den=sub(mul(aa,b),mul(a,bb));num=sub(b,bb);en=sub(a,aa)
  for name in ALL_ROWS:
   al,bl=row_coeff(name);value=add(den,scale(mul(al,num),-1),mul(bl,en))
   if value:rows.append(('projection_N_'+name,value))
 rows += [('den_nonnegative',den),('P_ge_one',sub(num,den)),('P_le_two',sub(scale(den,2),num)),('E_ge_zero',en),('E_le_one',sub(den,en))]
 rows=[(n,p)for n,p in rows if p]
 return den,num,en,rows

def projected_range_rows(b,label):
 den,num,en,_=projective_data(label)
 rows=[('range_P_lower',sub(num,scale(den,b[8].lo))),('range_P_upper',sub(scale(den,b[8].hi),num)),('range_E_lower',sub(en,scale(den,b[9].lo))),('range_E_upper',sub(scale(den,b[9].hi),en))]
 bl=label.split('|')[0]
 if bl!='B1':
  j=int(bl[1]);sgn=1 if bl[2]=='+'else -1
  vd=scale(var('v'+str(j)),sgn);qd=scale(var('q'+str(j)),sgn);bn=sub(poly(1),qd)
  rows += [('beta_range_lower',sub(bn,scale(vd,b[10].lo))),('beta_range_upper',sub(scale(vd,b[10].hi),bn))]
 return rows

def contract_projective(parent,label,rounds=8):
 out=contract_full(parent,label)
 if out['status']=='EMPTY':return out
 b=[I(*x)for x in out['aux_image']];den,num,en,new=projective_data(label)
 try:
  for it in range(rounds):
   prev=[x.data()for x in b]
   propagate(b,new+projected_range_rows(b,label)+CHARTS[label][0]+BASE_POLYS)
   direct_bounds(b,label);reconstruct_tail(b)
   hc=high_contract(b,rounds=2)
   if hc['status']=='EMPTY':raise Empty(hc['reason'])
   for i,v in enumerate(hc['aux_image']):meet(b,i,Q(v[0]),Q(v[1]))
   no=strict_impossible(label,b)
   if no:raise Empty(no)
   if prev==[x.data()for x in b]:break
  return {'status':'BOUNDED','aux_image':[x.data()for x in b],'rounds':it+1}
 except Empty as err:return {'status':'EMPTY','reason':str(err)}

def extended_rows(aux,label):
 """Keep old 38 shared products. Add only coefficient-pair monomials needed
 by the conditional projective prefix minors. All actual variables unchanged."""
 boxes=[I(*x)for x in aux];extra=projective_data(label)[3]+projected_range_rows(boxes,label)
 polys=BASE_POLYS+CHARTS[label][0]+extra
 pairs=sorted({m for _,p in polys for m in p if len(m)==2})
 if any(len(m)>2 for _,p in polys for m in p):raise AssertionError('degree > 2')
 ind={m:24+i for i,m in enumerate(pairs)};rows=[]
 for name,p in polys:
  a={};rhs=p.get((),Q(0))
  for m,c in p.items():
   if not m:continue
   j=m[0]if len(m)==1 else ind[m];a[j]=a.get(j,Q(0))-c
  rows.append((a,rhs))
 for pair,j in ind.items():
  i,k=pair;li,ui=boxes[i].lo,boxes[i].hi;lk,uk=boxes[k].lo,boxes[k].hi
  for ai,ak,az,bb in ((lk,li,-1,li*lk),(uk,ui,-1,ui*uk),(-uk,-li,1,-li*uk),(-lk,-ui,1,-ui*lk)):
   a={}
   for ix,c in ((i,ai),(k,ak),(j,Q(az))):a[ix]=a.get(ix,Q(0))+c
   rows.append((a,bb))
 boxes += [boxes[i]*boxes[k]for i,k in pairs]
 return rows,boxes
