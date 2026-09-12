#!/usr/bin/env python3
"""Independent symbolic identities, exact full-matrix controls, and negative tests.
No optimizer, sample-based proof of the local flow, or unreceived global tree.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,copy,sys,time
import sympy as sp
from local_model import NAMES,source,ev,diff,TAIL_MAPS,wall_transform,canonical_requirements
from native import to_matrix,from_matrix,verify_matrix,gates
from verify_local_certificate import verify
ROOT=Path(__file__).resolve().parent


def smodel(z):
 k,r,w,A,B,c,d,p,e,be=z[:10];u=z[10:13];x=z[13:16];v=z[16:19];q=z[19:22]
 D=sp.Matrix([[k,A,B],[c*k,r+c*A,r+c*B],[d*k,r+d*A,w+d*B]])
 S=D+sp.Matrix(x)*sp.Matrix([q]);O=S+sp.Matrix(u)*sp.Matrix([v])
 M=sp.Matrix([[1,-e]+v,[be,p-e*be]+[q[j]+be*v[j] for j in range(3)]]+[[u[i],p*x[i]-e*u[i]]+list(O.row(i))for i in range(3)])
 return M,D,S,O


def symbolic():
 z=list(sp.symbols(' '.join(NAMES), real=True));M,D,S,O=smodel(z);counts={}
 def zeros(expr,label):
  seq=list(expr)if isinstance(expr,(list,tuple,sp.MatrixBase))else[expr]
  for x in seq:assert sp.cancel(sp.expand(x))==0,(label,x)
  counts[label]=counts.get(label,0)+len(seq)
 # Independently enumerate every semantic physical slack with its original label.
 k,r,w,A,B,c,d,p,e,be=z[:10];u=z[10:13];x=z[13:16];v=z[16:19];q=z[19:22];pp={}
 def band(a,b,n):
  for value,suf in[(b-a,'+'),(b+a,'-')]:
   value=sp.expand(value)
   if value!=0:pp[n+suf]=value
 for value,n in[(e,'e'),(be,'beta'),(p-e*be,'head')]:band(value,1,n)
 for i in range(3):
  for value,b,n in[(u[i],1,'u'),(x[i],1,'x'),(v[i],1,'v'),(q[i],p,'q'),(p*x[i]-e*u[i],1,'L'),(q[i]+be*v[i],1,'P')]:band(value,b,n+str(i))
  for j in range(3):
   for T,b,n in[(D,k,'D'),(S,p,'S'),(O,1,'O')]:band(T[i,j],b,f'{n}{i}{j}')
 pp.update({'r+w':r+w,'r-w':r-w,'positive_p':p,'positive_k':k,'positive_r':r})
 sparse=source();assert set(pp)==set(sparse)
 for n,g in sparse.items():
  poly=sum((sp.Rational(c.numerator,c.denominator)*sp.prod(z[i]for i in mon)for mon,c in g.items()),sp.S(0))
  zeros(poly-pp[n],'semantic_physical_slacks')
  for i in range(22):
   dp=sum((sp.Rational(c.numerator,c.denominator)*sp.prod(z[j]for j in mon)for mon,c in diff(g,i).items()),sp.S(0))
   zeros(dp-sp.diff(pp[n],z[i]),'exact_derivative_dictionary')
 # Four maps are used only after reaching w=-r, never at a non-tied off-wall source.
 zz=list(z);zz[2]=-r;MW,DW,_,_=smodel(zz)
 for n,(L,R) in enumerate(TAIL_MAPS):
  Tleft=sp.eye(5);Tright=sp.eye(5);Tleft[3:5,3:5]=sp.Matrix(L);Tright[3:5,3:5]=sp.Matrix(R)
  new=wall_transform(zz,n);MN,DN,_,_=smodel(new)
  zeros(MN-Tleft*MW*Tright,'wall_full_matrix_maps')
  zeros(sp.Matrix(L)*sp.Matrix([[r,r],[r,-r]])*sp.Matrix(R)-sp.Matrix([[r,r],[r,-r]]),'wall_tail_CP_maps')
 # Actual low-r transpose, in both tail-sign branches. A'=epsilon*c*k.
 for sign in[-1,1]:
  ss=[1,sign,sign]
  new=[k,r,w,sign*c*k,sign*d*k,sign*A/k,sign*B/k,p,be,e]
  new += [ss[i]*v[i]for i in range(3)]+[-ss[i]*q[i]/p for i in range(3)]
  new += [ss[i]*u[i]for i in range(3)]+[-ss[i]*p*x[i]for i in range(3)]
  MN,DN,_,_=smodel(new);T=sp.diag(1,-1,1,sign,sign)
  zeros(MN-T*M.T*T,'low_r_actual_transpose')
  zeros([DN[i,j]-DN[i,0]*DN[0,j]/k-sp.Matrix([[r,r],[r,w]])[i-1,j-1]for i in(1,2)for j in(1,2)],'low_r_tail_and_boundary')
  zeros([new[7]*new[13]+q[0],-new[19]-p*x[0],new[8]*new[10]-be*v[0],new[0]-k,new[1]-r,new[2]-w],'low_r_type_and_G')
 return counts


def check_controls():
 data=json.loads((ROOT/'control_witnesses.json').read_text());cert=json.loads((ROOT/'local_wall_certificate.json').read_text());al=Q(json.loads((ROOT/'alpha.json').read_text())['isolating_interval']['lower']);gamma=Q(4132517,1000000)
 records=[]
 for rec in data['records']:
  ans=verify_matrix(rec['matrix']);z=ans['point'];F=ans['F'];case=rec['case'];cen=list(map(Q,cert['cases'][case]['center']))
  assert z==list(map(Q,rec['point'])) and F==Q(rec['F']) and gamma<F<al
  assert ans['strict_first_three'] and 2<z[0]<Q(21,10) and z[1]<z[0] and -z[1]<z[2]<z[1]
  assert max(abs(a-b)for a,b in zip(z,cen))<Q(cert['inner_radius'])
  L,R=gates(z);lp=all(x>0 for x in L);rp=all(x>0 for x in R)
  if case:assert not lp and not rp
  # Rank2 on both actual receiver sides (q/p scales a nonzero column only).
  u,x,v,q=z[10:13],z[13:16],z[16:19],z[19:22]
  assert any(u[i]*x[j]-u[j]*x[i]!=0 for i in range(3)for j in range(i+1,3))
  assert any(v[i]*q[j]-v[j]*q[i]!=0 for i in range(3)for j in range(i+1,3))
  k,r,w,A,B,c,d,p,e,be=z[:10]
  assert all(t!=0 for t in [e,be,A,B,c,d]+u+x+v+q)
  left_cof=[u[0]-be*x[0],u[1]-be*x[1],be*x[2]-u[2],u[0]*x[1]-x[0]*u[1],u[0]*x[2]-x[0]*u[2],u[1]*x[2]-x[1]*u[2]]
  right_cof=[p*v[0]+e*q[0],p*v[1]+e*q[1],-e*q[2]-p*v[2],v[0]*q[1]-q[0]*v[1],v[0]*q[2]-q[0]*v[2],v[1]*q[2]-q[1]*v[2]]
  assert all(t!=0 for t in left_cof+right_cof)
  assert not all([A*c>=0,A*d>=0,c*d>=0,u[1]*u[2]<=0])
  assert not all([A*c>=0,B*c>=0,A*B>=0,v[1]*v[2]<=0])
  records.append({'case':case,'F':str(F),'gamma_gap':str(F-gamma),'alpha_lower_gap':str(al-F),'left_pass':lp,'right_pass':rp,'rank22':True,'generic_cofactors':True,'strict_first_three':True})
 # A real r=k source with c<0 and another c=0 show why the high-r fixed Q rule cannot be blindly reused.
 boundary_checks=0
 for c0 in [Q(-1,10),Q(0),Q(1,10)]:
  zz=[Q(1),Q(1),Q(-1),Q(0),Q(0),c0,Q(0),Q(1),Q(0),Q(0)]+[Q(0)]*12
  MM=to_matrix(zz);verify_matrix(MM)
  sign=-1 if c0>0 else 1;t=[1,-1,1,sign,sign]
  TT=[[t[i]*MM[j][i]*t[j]for j in range(5)]for i in range(5)];qz=verify_matrix(TT)['point']
  assert qz[3]<=0 and qz[0]==qz[1]==1 and qz[1]-qz[2]==2;boundary_checks+=1
 off=json.loads((ROOT/'strict_offwall_control.json').read_text());answer=verify_matrix(off['matrix']);zz=answer['point'];ff=answer['F'];au=Q(json.loads((ROOT/'alpha.json').read_text())['isolating_interval']['upper'])
 assert zz==list(map(Q,off['point'])) and ff==Q(off['F']) and gamma<ff<al<au<2*zz[1]
 assert answer['strict_first_three'] and zz[1]<zz[0] and 2<zz[0]<Q(21,10) and -zz[1]<zz[2]<zz[1]
 from alpha_ports import proves
 bb=[(x,x)for x in zz]+[(zz[8]*zz[10],zz[8]*zz[10])]
 assert proves(bb,1) and not proves(bb,4) and not proves(bb,5)
 gl,gr=gates(zz);assert not all(t>0 for t in gl) and not all(t>0 for t in gr)
 return {'records':records,'r_equals_k_zero_sign_boundary_checks':boundary_checks,'nontrivial_offwall_control':{'F':str(ff),'r':str(zz[1]),'k':str(zz[0]),'r_above_alpha_half':True,'strict_first_three':True,'old_both_gates_fail':True,'not_weak_R0_or_2r_exit':True,'certified_local_flow_exit':1}}



def negative_certificate_tests():
 cert=json.loads((ROOT/'local_wall_certificate.json').read_text());cases=[]
 def reject(label,mut):
  bad=copy.deepcopy(cert);mut(bad)
  try:verify(bad)
  except (AssertionError,ValueError,KeyError):cases.append(label);return
  raise AssertionError('bad certificate accepted: '+label)
 reject('wrong schema',lambda c:c.update(schema='untrusted'))
 reject('missing chart',lambda c:c['cases'].pop())
 reject('wrong coordinate order',lambda c:c['coordinate_order'].reverse())
 reject('too large inner box',lambda c:c.update(inner_radius='1/1000'))
 reject('negative gain',lambda c:c.update(uniform_height_gain='-1'))
 reject('unsupported larger gain',lambda c:c.update(uniform_height_gain='1'))
 reject('invalid inverse',lambda c:c['cases'][0]['inverse_preconditioner'][0].__setitem__(0,'12345'))
 reject('missing delta',lambda c:c['cases'][0]['active_labels'].__setitem__(20,'positive_p'))
 reject('duplicate active band',lambda c:c['cases'][1]['active_labels'].__setitem__(0,c['cases'][1]['active_labels'][1]))
 reject('center off wall',lambda c:c['cases'][2]['center'].__setitem__(2,'0'))
 for value in [True,1.0]:
  try:to_matrix([value]+[0]*21)
  except TypeError:cases.append('nonexact scalar '+repr(value))
  else:raise AssertionError('nonexact input accepted')
 return cases


def main():
 t=time.time();result={'status':'V35_SYMBOLIC_CONTROLS_AND_NEGATIVE_TESTS_PASS','symbolic_counts':symbolic(),'controls':check_controls(),'rejected_bad_inputs':negative_certificate_tests()};result['seconds']=time.time()-t;print(json.dumps(result,indent=2))
if __name__=='__main__':main()
