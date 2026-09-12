from pathlib import Path
import sys,json
import sympy as s
from itertools import combinations
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from build_models import make_model
k,r,w,A,B,c,d,p,e,be=s.symbols('k r w A B c d p e be')
u=s.symbols('u0:3');x=s.symbols('x0:3');v=s.symbols('v0:3');q=s.symbols('q0:3')
count=0
def zero(expr):
 global count
 assert s.expand(expr)==0;count+=1
packets=[s.Matrix([1,*x])*s.Matrix([p,*q]).T,s.Matrix([be,*u])*s.Matrix([e,*v]).T,s.Matrix([c,d])*s.Matrix([k,A,B]).T]
for P in packets:
 for ii in combinations(range(P.rows),2):
  for jj in combinations(range(P.cols),2):zero(P[ii[0],jj[0]]*P[ii[1],jj[1]]-P[ii[0],jj[1]]*P[ii[1],jj[0]])
 for ii in combinations(range(P.rows),3):
  for jj in combinations(range(P.cols),3):zero(s.prod(P[ii[t],jj[t]]for t in range(3))-s.prod(P[ii[t],jj[(t+1)%3]]for t in range(3)))
 if P.rows==P.cols==4:zero(s.prod(P[t,t]for t in range(4))-s.prod(P[t,(t+1)%4]for t in range(4)))
D=s.Matrix([[k,A,B],[c*k,r+c*A,r+c*B],[d*k,r+d*A,w+d*B]])
S=D+s.Matrix(x)*s.Matrix(q).T;O=S+s.Matrix(u)*s.Matrix(v).T
for i in range(3):
 zero(packets[0][i+1,0]-p*x[i]);zero(packets[1][i+1,0]-e*u[i]);zero(packets[1][0,i+1]-be*v[i])
 for j in range(3):zero(S[i,j]-D[i,j]-packets[0][i+1,j+1]);zero(O[i,j]-S[i,j]-packets[1][i+1,j+1])
for i in range(2):
 for j in range(3):zero(D[i+1,j]-packets[2][i,j]-(0 if j==0 else w if(i==1 and j==2)else r))
J=s.symbols('J');a,b,t=s.symbols('a b t');chi=c*a
zero(J*d*b-t*t-((J-chi)*d*b+(c*b-t)*d*a+t*(d*a-t)))
zero(J*chi-t*t-((J-t)*chi+t*(chi-t)))
zero(k-B-r-((k-D[1,2])+(1-c)*(-B)))
zero(k*(1+c)-r-((k-D[1,1])+c*(k+A)))
zero(k*(1+d)-r-((k-D[2,1])+d*(k+A)))
zero(2*k-r+w-B-((k-D[1,2])+(k+D[2,2])+(1-c+d)*(-B)))
for sval,slope,intercept in [(s.Rational(3,4),-s.Rational(15,16),s.Rational(6075,1024)),(s.Rational(3,5),-s.Rational(9,5),s.Rational(972,125)),(s.Rational(1,2),-s.Rational(21,8),s.Rational(1225,128))]:
 kk=(9-sval*sval)/4;R=kk*(3+sval)/2;der=(3+sval)/2-kk/sval
 zero(der-slope);zero(R-der*kk-intercept)
ROOT=Path(__file__).resolve().parents[1]
modelchecks={}
for path in sorted((ROOT/'models').iterdir()):
 if not(path/'model.json').exists():continue
 data=json.loads((path/'model.json').read_text());re=make_model(data['K'],data['J'],data['type'],data['branch']);assert re==data
 assert sum(row['name'].startswith('G_def')for row in data['rows'])==2
 vs=tuple(s.Symbol(z)for z in data['variables']);env=dict(zip(data['variables'],vs));mons=list(vs)+[vs[i]*vs[j]for i,j in data['pairs']]
 for row in data['rows']:
  zero(s.Rational(row['positive_scale'])*s.sympify(row['polynomial'],locals=env)-(row['rhs']-sum(z*co for z,co in zip(mons,row['coefficients']))))
 modelchecks[path.name]={'rows':len(data['rows']),'products':len(data['pairs']),'source_equal':True}
print(json.dumps({'status':'SYMBOLIC_DICTIONARY_AND_NEW_HIGH_ROOT_ROWS_PASS','exact_zero_assertions':count,'models':modelchecks}))
