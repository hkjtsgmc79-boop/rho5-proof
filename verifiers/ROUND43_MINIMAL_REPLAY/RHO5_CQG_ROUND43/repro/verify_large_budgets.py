"""Exact identities and a full V32 matrix regression for the new necessity chain."""
from pathlib import Path
from fractions import Fraction as Q
import json, argparse
import sympy as s
from build_large_model import model

ROOT=Path(__file__).resolve().parent
checks={}
def check(name,expr):
    assert s.cancel(s.expand(expr))==0,name
    checks[name]=True

k,r,w,A,B,c,d,p,e,be=s.symbols('k r w A B c d p e be')
u=s.Matrix(s.symbols('u0:3'));x=s.Matrix(s.symbols('x0:3'))
v=s.Matrix(s.symbols('v0:3'));q=s.Matrix(s.symbols('q0:3'))
D=s.Matrix([[k,A,B],[c*k,r+c*A,r+c*B],[d*k,r+d*A,w+d*B]])
S=D+x*q.T;O=S+u*v.T;L=p*x-e*u;P=q+be*v
M=s.Matrix.vstack(s.Matrix([[1,-e,*v]]),s.Matrix([[be,p-e*be,*P]]),u.row_join(L).row_join(O))
stage=M[1:,1:]-M[1:,0]*M[0,1:]
want=s.Matrix.vstack(s.Matrix([[p,*q]]),(p*x).row_join(S))
for i in range(4):
    for j in range(4):check(f'first_schur_{i}{j}',stage[i,j]-want[i,j])
core=want[1:,1:]-want[1:,0]*want[0,1:]/p
for i in range(3):
    for j in range(3):check(f'second_schur_{i}{j}',core[i,j]-D[i,j])
H=D[1:,1:]-D[1:,0]*D[0,1:]/k
for i in range(2):
    for j in range(2):check(f'third_schur_{i}{j}',H[i,j]-[[r,r],[r,w]][i][j])
check('rAc_slack',k-A-r-((k-D[1,1])+(1-c)*(-A)))
check('core_parabola_square',2*k*r-r*r+k*w+(r-s.Rational(3,2)*k)**2-k*(s.Rational(9,4)*k-r+w))
check('stage_parabola_scaling',p*p*((k/p)*(3-k/p)-r/p)-(3*p*k-k*k-p*r))

# All three sign normalizations are actual simultaneous row/column sign changes.
maps=[
    ({e:-e,be:-be,**{xi:-xi for xi in x},**{qi:-qi for qi in q}},[1,-1,1,1,1]),
    ({A:-A,B:-B,c:-c,d:-d,u[0]:-u[0],x[0]:-x[0],v[0]:-v[0],q[0]:-q[0]},[1,1,-1,1,1]),
    ({**{z:-z for z in list(u)+list(x)+list(v)+list(q)}},[1,1,-1,-1,-1]),
]
for n,(sub,sgn) in enumerate(maps):
    diag=s.diag(*sgn);diff=M.subs(sub,simultaneous=True)-diag*M*diag
    for i in range(5):
        for j in range(5):check(f'physical_sign_map_{n}_{i}{j}',diff[i,j])

# The symmetric H makes mixed head cases II and III exact transposes.
trans={e:be,be:e,A:c*k,B:d*k,c:A/k,d:B/k}
trans.update({u[i]:v[i] for i in range(3)})
trans.update({v[i]:u[i] for i in range(3)})
trans.update({x[i]:-q[i]/p for i in range(3)})
trans.update({q[i]:-p*x[i] for i in range(3)})
J=s.diag(1,-1,1,1,1)
diff=M.subs(trans,simultaneous=True)-J*M.T*J
for i in range(5):
    for j in range(5):check(f'II_III_physical_transpose_{i}{j}',diff[i,j])
tailflip={A:-A,B:-B,c:-c,d:-d}
tailflip.update({z:-z for arr in (u,x,v,q) for z in arr[1:,0]})
T=s.diag(1,1,1,-1,-1)
diff=M.subs(tailflip,simultaneous=True)-T*M*T
for i in range(5):
    for j in range(5):check(f'head_preserving_A_sign_{i}{j}',diff[i,j])
check('transpose_b_equals_h',(p*x[0]).subs(trans,simultaneous=True)+q[0])
check('transpose_h_equals_b',(-q[0]).subs(trans,simultaneous=True)-p*x[0])

# Core parabola nonnegative numerator identity in the r>k branch.
a,b,cc,dd,z,om=s.symbols('a b cc dd z om')
rhs=(b*cc-z)*a*dd+z*(a*dd-z)+z*z*(1-a*cc)+a*cc*(1+om-b*dd)
check('core_parabola_positive_decomposition',a*cc*(1+om-z*z)-rhs)

# Full regression from the same original rational 5x5 matrix; no independent completion.
data=json.loads((ROOT/'strict_witness.json').read_text())
N=s.Matrix([[s.Rational(t) for t in row] for row in data['matrix']])
st=N[1:,1:]-N[1:,0]*N[0,1:]
pv=st[0,0];ev=-N[0,1];bv=N[1,0]
uv=N[2:,0];xv=st[1:,0]/pv;vv=N[0,2:].T;qv=st[0,1:].T
dv=st[1:,1:]-st[1:,0]*st[0,1:]/pv;kv=dv[0,0]
hv=dv[1:,1:]-dv[1:,0]*dv[0,1:]/kv
vals=[kv,hv[0,0],hv[1,1],dv[0,1],dv[0,2],dv[1,0]/kv,dv[2,0]/kv,pv,ev,bv]+list(uv)+list(xv)+list(vv)+list(qv)
vs,_,rows,_,_,f=model(s.Rational(21,10));sub=dict(zip(vs,vals))
physical=[(n,pol.as_expr().subs(sub)) for n,pol in rows if n!='F']
assert all(t>=0 for _,t in physical),[(n,str(t)) for n,t in physical if t<0]
alpha=json.loads((ROOT/'alpha.json').read_text())
assert Q(str(f))<Q(alpha['isolating_interval']['lower'])
result=dict(schema='rho5.cqg.r43.analytic-audit.v1',status='R43_EXACT_NECESSITY_CHAIN_AUDIT_PASS',
            identities=len(checks),checks=checks,
            v32_nonnegative_necessary_rows=len(physical),
            v32_budget_slacks={n:str(t) for n,t in physical if 'parabola' in n or n in ('w_plus_k','rAc')},
            q=str(f),q_below_alpha=True,proof_scope='Identity audit plus full rational regression; general implication follows the accompanying analytic proof, not a finite test.')
ap=argparse.ArgumentParser();ap.add_argument('--output');args=ap.parse_args()
Path(args.output or ROOT/'R43_ANALYTIC_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('checks','v32_budget_slacks')}))
