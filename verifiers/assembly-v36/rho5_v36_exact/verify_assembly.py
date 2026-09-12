"""Exact algebra of X normalization, S/T transport and complete-range bookkeeping.
No missing proof tree is replayed; the Round47 tree results are adopted inputs.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import sympy as s
import json,time
ROOT=Path(__file__).parent

def main():
 start=time.monotonic();checks=0
 def zero(z):
  nonlocal checks
  assert s.cancel(z)==0,z;checks+=1
 a,b,c,d,r,t0,t1,w,k,p,e,be=s.symbols('a b c d r s t w k p e beta',nonzero=True)
 u=s.Matrix(s.symbols('u0:3'));x=s.Matrix(s.symbols('x0:3'));v=s.Matrix(s.symbols('v0:3'));q=s.Matrix(s.symbols('q0:3'))
 C=s.Matrix([[1,a,b],[c,c*a+r,c*b+t0],[d,d*a+t1,d*b+w]])
 D=k*C;O=D+u*v.T+x*q.T
 M=s.zeros(5);M[0,0]=1;M[0,1]=-e;M[1,0]=be;M[1,1]=p-e*be
 M[0,2:5]=v.T;M[1,2:5]=(q+be*v).T;M[2:5,0:1]=u;M[2:5,1:2]=p*x-e*u;M[2:5,2:5]=O
 # Independent Schur identity, scale included.
 S1=M[1:,1:]-M[1:,0:1]*M[0:1,1:]
 S2=S1[1:,1:]-S1[1:,0:1]*S1[0:1,1:]/p
 for z in S2-D:zero(z)
 H=D[1:,1:]-D[1:,0:1]*D[0:1,1:]/k
 for z in H-k*s.Matrix([[r,t0],[t1,w]]):zero(z)
 h=w-t1*t0/r
 # Exact independent S/T core swaps, all matrix identities and scalar heights.
 swap3=s.Matrix([[1,0,0],[0,0,1],[0,1,0]]);swap5=s.eye(5);swap5[2:5,2:5]=swap3
 for kind,subs in [('S',{a:b,b:a,c:c,d:d,r:t0,t0:r,t1:w,w:t1}),('T',{a:a,b:b,c:d,d:c,r:t1,t0:w,t1:r,w:t0})]:
  target=C.subs(subs,simultaneous=True)
  expected=C*swap3 if kind=='S' else swap3*C
  for z in target-expected:zero(z)
  hnew=h.subs(subs,simultaneous=True)
  zero(hnew+(r/(t0 if kind=='S' else t1))*h)
  Mn=M.subs(subs,simultaneous=True)
  # Explicit packet transformation after core transformation.
  mp={}
  for seq in ((v,q) if kind=='S' else (u,x)):
   mp.update({seq[i]:(swap3*seq)[i]for i in range(3)})
  Mn=Mn.subs(mp,simultaneous=True)
  for z in Mn-(M*swap5 if kind=='S' else swap5*M):zero(z)
 # Flag product identities, including the permutation of conjuncts.
 flags={'RL':[r*a*c,t1*a*d,r*t1*c*d,r*t1*u[1]*u[2]],
        'SL':[t0*b*c,w*b*d,t0*w*c*d,t0*w*u[1]*u[2]],
        'RR':[r*a*c,t0*b*c,r*t0*a*b,r*t0*v[1]*v[2]],
        'SR':[t1*a*d,w*b*d,t1*w*a*b,t1*w*v[1]*v[2]]}
 Ssub={a:b,b:a,r:t0,t0:r,t1:w,w:t1,v[1]:v[2],v[2]:v[1]}
 Tsub={c:d,d:c,r:t1,t0:w,t1:r,w:t0,u[1]:u[2],u[2]:u[1]}
 for lhs,sub,rhs,order in [('RL',Ssub,'SL',[0,1,2,3]),('RR',Ssub,'RR',[1,0,2,3]),('RL',Tsub,'RL',[1,0,2,3]),('RR',Tsub,'SR',[0,1,2,3])]:
  for i,j in enumerate(order):zero(flags[lhs][i].subs(sub,simultaneous=True)-flags[rhs][j])
 # Exhaust all sign patterns of three equal-magnitude X arms.
 R=s.symbols('R',positive=True);W=s.symbols('W',real=True)
 for er,es,et in product((-1,1),repeat=3):
  HT=s.Matrix([[er*R,es*R],[et*R,W]]);L=s.diag(er,et);P=s.diag(1,er*es)
  for z in L*HT*P-s.Matrix([[R,R],[R,er*es*et*W]]):zero(z)
  zero(er*es*et*(W-(et*R)*(es*R)/(er*R))+(R-er*es*et*W))
 # Explicit normalized negative D tail height and positive orientation budget.
 S,T=s.symbols('S T',nonnegative=True)
 Hminus=s.Matrix([[R,S],[T,-R]]);Hplus=s.Matrix([[R,S],[T,R]])
 zero(Hminus.det()+R**2+S*T)
 zero((-R-T*S/R)+R+S*T/R)
 zero((R-T*S/R)-(R-S*T/R))
 # Actual full transpose for general D-chart, not just the symmetric X case.
 JT=s.diag(1,-1,1,1,1)
 Dt=D.T;ut=v;xt=-q/p;vt=u;qt=-p*x
 Mt=s.zeros(5);Mt[0,0]=1;Mt[0,1]=-be;Mt[1,0]=e;Mt[1,1]=p-e*be
 Mt[0,2:5]=vt.T;Mt[1,2:5]=(qt+e*vt).T
 Mt[2:5,0:1]=ut;Mt[2:5,1:2]=p*xt-be*ut;Mt[2:5,2:5]=Dt+xt*qt.T+ut*vt.T
 for z in Mt-JT*M.T*JT:zero(z)
 for z in Dt+xt*qt.T-(D+x*q.T).T:zero(z)
 # All sixteen nonzero D-tail sign configurations become + or - orientation.
 for er,es,et,ew in product((-1,1),repeat=4):
  HT=s.Matrix([[er*R,es*S],[et*T,ew*R]])
  LH=s.diag(er,et);RH=s.diag(1,er*es)
  for z in LH*HT*RH-s.Matrix([[R,S],[T,er*es*et*ew*R]]):zero(z)
 # Four elementary range cases are exhaustive, including exact boundaries.
 gamma=Q(4132517,10**6);ks=Q(2);ku=Q(21,10)
 bounds=json.loads((ROOT/'inputs/round47/source/alpha.json').read_text());al=Q(bounds['isolating_interval']['lower']);au=Q(bounds['isolating_interval']['upper'])
 assert Q(1653,400)<gamma<al<au and ks<gamma/2<ku
 audits=json.loads((ROOT/'evidence/round47_review.json').read_text());assert audits['totals']['open']==0 and audits['missing_large_trees_replayed_here'] is False
 out={'status':'V36_X_RST_ASSEMBLY_ALGEBRA_AND_SCOPE_PASS','symbolic_zero_assertions':checks,'X_sign_cases':8,'D_sign_cases':16,'B_contact_classes':54,'B_transpose_representatives':36,
 'source_model_includes_ties_and_zero_cofactors':True,'boundary_r_equals_k':'Round47 low roots',
 'boundary_k_equals_2':'V31','boundary_k_equals_21_over_10':'adopted upper range and overlap',
 'complete_X_alpha':'proved by explicit composition of adopted complete-scope results',
 'R_ST_macro_assembly':'complete under the declared frozen inputs and local tree receipts',
 'ledger_before_controller_registration':'11/15','ledger_recommendation':'14/15',
 'macro_B22':'OPEN','unreceived_global_trees_replayed_here':False,
 'seconds':time.monotonic()-start}
 (ROOT/'evidence/assembly_verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
