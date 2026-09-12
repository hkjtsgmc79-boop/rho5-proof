"""Symbolic identities and independent exact controls; not full formalization."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import random,json
import sympy as sp
from protocol import *
from capacity import capacity,check_complete
from interval_capacity import root_box

def run():
 counters={};a,b,c,d,p,e,al,bl=sp.symbols('a b c d p e al bl')
 den=c*b-a*d;num=b-d;en=a-c;gi=1-a*p+b*e;gj=1-c*p+d*e
 identities=[den*p-num-d*gi+b*gj,den*e-en-c*gi+a*gj,
             den*(1-al*p+bl*e)-(den-al*num+bl*en)+al*(den*p-num)-bl*(den*e-en)]
 P=num/den;E=en/den
 desired=[d*num,-b*num,d*(c-a),b*(a-c),c*num,-a*num,-c*en,a*en]
 for f,v,target in zip([P]*4+[E]*4,[a,c,b,d]*2,desired):identities.append(sp.cancel(sp.diff(f,v)*den**2-target))
 for item in identities:assert sp.cancel(item)==0
 counters['primitive_projection_and_derivative_identities']=len(identities)
 # Independently validate ALL coefficient-generated source homogenizations.
 symbols=sp.symbols(' '.join(NAMES));mapping=dict(zip(NAMES,symbols))
 def expr(poly):
  return sp.Add(*(sp.Rational(v.numerator,v.denominator)*sp.prod(symbols[i]for i in m)for m,v in poly.items()))
 count=0;maxdeg=0
 for pre in PREFIX_LABELS:
  for beta_lab in ('B1','B0+'):
   lab=beta_lab+'|'+pre;dd,nn,mm,projected=projective_data(lab);D,Nn,Mm=map(expr,(dd,nn,mm));parts=pre.split(':');ai,bi=map(expr,row_coeff(parts[1]));gs=1-ai*symbols[8]+bi*symbols[9]
   if parts[0]=='N':
    aj,bj=map(expr,row_coeff(parts[2]));gt=1-aj*symbols[8]+bj*symbols[9]
    dp=bj*gs-bi*gt;de=aj*gs-ai*gt
   else:dp=-gs+bi*(symbols[9]-1);de=ai*(symbols[9]-1)
   by=dict(homogeneous_rows(lab))
   for name,source in BASE_POLYS:
    g=expr(source);gp=sp.diff(g,symbols[8]);ge=sp.diff(g,symbols[9])
    if gp==0 and ge==0:continue
    g0=sp.expand(g-symbols[8]*gp-symbols[9]*ge)
    expected=sp.expand(D*g0+Nn*gp+Mm*ge)
    assert sp.expand(D*g-expected-dp*gp-de*ge)==0;count+=1
    if beta_lab=='B1':expected=expected.subs(symbols[10],1)
    got=by.get('homogenized_'+name,{})
    assert sp.expand(expected-expr(got))==0;count+=1
   for _,pol in homogeneous_rows(lab):maxdeg=max(maxdeg,max(map(len,pol),default=0))
 counters['all_source_homogenization_identity_checks']=count;counters['max_projected_source_degree']=maxdeg
 # Independent ordered coefficient-polytope vertices (not derivative code).
 from sharp_prefix import pair_ranges
 rng=random.Random(404049);nbox=400
 for n in range(nbox):
  aa=sorted([Q(rng.randrange(1,25),24),Q(rng.randrange(1,25),24)])
  cc=sorted([Q(rng.randrange(1,25),24),Q(rng.randrange(1,25),24)])
  if aa[1]<cc[0]:aa,cc=cc,aa
  bb=sorted([Q(rng.randrange(1,25),24),Q(rng.randrange(1,25),24)])
  dd=sorted([-Q(rng.randrange(1,25),24),-Q(rng.randrange(1,25),24)])
  verts={(x,y)for x in aa for y in cc if x>=y}
  ll=max(aa[0],cc[0]);uu=min(aa[1],cc[1])
  if ll<=uu:verts.update([(ll,ll),(uu,uu)])
  assert verts
  vals=[((bbv-ddv)/(y*bbv-x*ddv),(x-y)/(y*bbv-x*ddv))for x,y in verts for bbv in bb for ddv in dd]
  rr=pair_ranges(I(*aa),I(*bb),I(*cc),I(*dd))
  assert rr['p_lower']==min(v[0]for v in vals)and rr['p_upper']==max(v[0]for v in vals)
  assert rr['e_lower']==min(v[1]for v in vals)and rr['e_upper']==max(v[1]for v in vals)
 counters['independent_ordered_polytope_range_tests']=nbox
 # Exact interval example in the most common H/L0 basis.
 rr=pair_ranges(I(1),I(1),I(Q(1,4),Q(1,2)),I(-1,Q(-1,2)))
 assert rr=={'p_lower':Q(4,3),'p_upper':Q(2),'e_upper':Q(1),'e_lower':Q(1,3)}
 # Denominator touching zero -> no fake finite bound or division.
 zero=pair_ranges(I(Q(1,2),1),I(0,1),I(0,Q(1,2)),I(-1,0))
 assert zero['p_upper'] is None and zero['e_upper'] is None
 counters['zero_denominator_and_order_boundary_controls']=2
 # Existing gamma-high ACTUAL canonical matrices must survive all new rows.
 src=json.loads((bootstrap.V39/'inputs/evidence/capacity_controls.json').read_text());controls=contain=poly_checks=lift_checks=0
 for old in src:
  f=[Q(x)for x in old['maximum']['frame']]
  if f[8]<0:f=f[:5]+[-x for x in f[5:]]
  out=capacity(f);assert out['status']=='COMPLETE_FIXED_FRAME_MAXIMUM'
  gap=[Q(x)for x in out['point_gap']];check_complete(gap);assert out['tail']['F']>GAMMA
  aux=[gap[0],gap[1],gap[1]-gap[22],gap[1]-gap[23],*gap[3:22],out['tail']['F']]
  u,x,v,q=[f[j:j+3]for j in(5,8,11,14)];beta,Pp,Ee=[out['prefix'][n]for n in('beta','p','e')]
  labs=exact_labels(u,x,v,q,beta,Pp,Ee);assert labs
  for lab in labs:
   pols=projective_data(lab)[3]+homogeneous_rows(lab)
   for _,pol in pols:assert eval_point(pol,aux)>=0;poly_checks+=1
   # Direct check of lifted row system on the actual singleton image.
   singleton=[[str(z),str(z)]for z in aux]
   rows,boxes=generalized_rows(singleton,lab)
   # all boxes singleton -> their values ARE the actual monomials
   assert all(t.lo==t.hi for t in boxes)
   point=[v.lo for v in boxes]
   for aa,bb in rows:assert sum(c*point[i]for i,c in aa.items())<=bb;lift_checks+=1
  for radius in (Q(0),Q(1,100000),Q(1,1000)):
   bx=[[str(max(rt.lo,z-radius)),str(min(rt.hi,z+radius))]for z,rt in zip(f,root_box())]
   parent=parent_enclosure(bx);assert parent['status']!='EMPTY'
   for lab in labs:
    for mode,fn in MODES.items():
     zz=fn(parent,lab);assert zz['status']=='BOUNDED',(controls,lab,mode,radius,zz)
     assert all(Q(l)<=a0<=Q(h)for a0,(l,h)in zip(aux,zz['aux_image'])),(controls,lab,mode,radius)
     contain+=1
  controls+=1
 counters.update(existing_complete_gamma_high_controls=controls,exact_new_source_row_checks=poly_checks,
                 exact_lifted_inequality_checks=lift_checks,point_and_positive_width_containment_checks=contain,
                 new_full_domain_height_claim=False)
 return counters
if __name__=='__main__':print(json.dumps(run(),indent=2))
