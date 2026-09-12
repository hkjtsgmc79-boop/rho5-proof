"""Exact audit of the actual III->II interface; no new leaf rule or height claim."""
from pathlib import Path
import json,sys
import sympy as s

out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
names=['k','r','w','A','B','c','d','p','e','beta']+[f'{t}{j}' for t in ('u','x','v','q') for j in range(3)]
z=dict(zip(names,s.symbols(' '.join(names))));k,p=z['k'],z['p'];count=0
def blocks(t):
 k,r,w,A,B,c,d,p,e,be=[t[n] for n in names[:10]]
 u,x,v,q=[s.Matrix([t[f'{label}{j}'] for j in range(3)]) for label in ('u','x','v','q')]
 D=s.Matrix([[k,A,B],[c*k,r+c*A,r+c*B],[d*k,r+d*A,w+d*B]])
 S=D+x*q.T;O=S+u*v.T
 M=s.zeros(5);M[0,0]=1;M[0,1]=-e;M[1,0]=be;M[1,1]=p-e*be
 for i in range(3):
  M[i+2,0]=u[i];M[0,i+2]=v[i];M[i+2,1]=p*x[i]-e*u[i];M[1,i+2]=q[i]+be*v[i]
  for j in range(3):M[i+2,j+2]=O[i,j]
 return M,D,S,O
def transform(t):
 k,p=t['k'],t['p'];q=dict(t)
 q.update(A=-k*t['c'],B=-k*t['d'],c=-t['A']/k,d=-t['B']/k,e=t['beta'],beta=t['e'])
 for i,sign in enumerate((1,-1,-1)):
  q[f'u{i}']=sign*t[f'v{i}'];q[f'v{i}']=sign*t[f'u{i}']
  q[f'x{i}']=-sign*t[f'q{i}']/p;q[f'q{i}']=-sign*p*t[f'x{i}']
 return q
def zero(expr):
 global count
 assert s.cancel(expr)==0;count+=1
def same(a,b):
 for x in a-b:zero(x)
t=transform(z);M,D,S,O=blocks(z);N,E,T,U=blocks(t)
J=s.diag(1,-1,1,1,1);Q=s.diag(1,1,1,-1,-1);Z=s.diag(1,-1,-1)
same(N,Q*J*M.T*J*Q)
same(E,Z*D.T*Z);same(T,Z*S.T*Z);same(U,Z*O.T*Z)
same(s.Matrix([[t['r'],t['r']],[t['r'],t['w']]]),s.Matrix([[z['r'],z['r']],[z['r'],z['w']]]))
zero(N[:2,:2].det()-p);zero(t['k']-k);zero(t['r']-t['w']-(z['r']-z['w']))
zero(p*t['x0']-(-z['q0']));zero(-t['q0']-p*z['x0'])
zero(t['e']*t['beta']-z['e']*z['beta'])
zero(t['e']*t['u0']-z['beta']*z['v0'])
twice=transform(t)
for name in names:zero(twice[name]-z[name])
# Positive p,k are required; these are algebraic interface controls, not invented physical high points.
negative=[]
bad=dict(t);bad['q0']=-z['x0']
assert any(s.cancel(x)!=0 for x in blocks(bad)[0]-N);negative.append('missing_p_in_q_transform_rejected')
bad=dict(t);bad['x0']=-z['q0']
assert any(s.cancel(x)!=0 for x in blocks(bad)[0]-N);negative.append('missing_inverse_p_in_x_transform_rejected')
assert s.cancel(t['e']*t['u0']-z['e']*z['u0'])!=0;negative.append('wrong_III_source_G_rejected')
result={'status':'ACTUAL_HIGH_BRANCH_TRANSPOSE_INTERFACE_PASS','exact_zero_checks':count,'negative_controls':negative,
 'actual_map':'Q J0 M^T J0 Q, J0=diag(1,-1,1,1,1), Q=diag(1,1,1,-1,-1)',
 'native_map':{n:str(t[n]) for n in names},'preserved':['p','k','r','w','F','all absolute M/S/D bands','symmetric H'],
 'III_to_II':'b_new=h_old>=1; h_new=b_old<=1; u0_new=v0_old>0; v0_new=u0_old<0; G_new=beta_old*v0_old',
 'high_signs':'A_new=-k*c<=0, B_new=-k*d<=0, c_new=-A/k>=0, d_new=-B/k>=0 for positive k and old high signs',
 'I_quotient':'u0,v0 exchange, so either source or its actual transpose has u0>=v0',
 'boundary':'Only actual k>2,r>k responsibility; closed high-sign outer roots do not cover arbitrary r=k sources',
 'new_height_credit':False}
(out/'TRANSPOSE_INTERFACE_RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
