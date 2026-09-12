"""Symbolic identities only; signs and flow continuation proved in THEOREMS.md."""
import sympy as S
import json
r,s,t=S.symbols('r s t',positive=True);g=r-s;h=s-t;Z=2*r+t-s
R=(r*r+s*t)/Z;T=R*(r+2*t-s)/(r+s);mu=g/Z;lam=1-mu;nu=(r-R)/(r+s);xi=1-nu
K=lam*xi+mu*nu;FX=R+T;delta=R-T;F=r+s*t/r;theta=g/(2*r)
checks=[]
def eq(a,b,name):
 if S.cancel(a-b)!=0:raise AssertionError(name)
 checks.append(name)
eq(F-FX,theta*delta,'same-source loss')
eq(F-FX,g*R*h/(r*(r+s)),'positive loss formula')
eq(delta,2*R*h/(r+s),'X wall gap')
eq(mu-theta,g*h/(2*r*Z),'theta <= mu')
eq(nu,mu*(r+t)/(r+s),'nu dictionary')
eq(mu-nu,mu*h/(r+s),'nu <= mu')
eq(1-2*mu,(s+t)/Z,'mu <= 1/2')
eq(R-r/2,(r*h+2*s*t)/(2*Z),'R >= r/2')
eq(r-R,g*(r+t)/Z,'R <= r')
M=S.Matrix([[lam,-mu],[-nu,-xi]])*S.Matrix([[r,s],[t,-r]])*S.Matrix([[0,1],[1,0]])
for i in range(2):
 for j in range(2):eq(M[i,j],S.Matrix([[R,R],[R,-T]])[i,j],f'actual tail {i}{j}')
x,y,a,b=S.symbols('x y a b');hp=1-x;hm=1+y
strip=xi*hp+mu*hm-2*mu*xi
eq(strip,K-xi*x+mu*y,'inverse-strip deficit')
eq(strip+mu*(xi-hm),xi*(hp-mu),'one-slack budget')
eq((xi*(lam*a-mu*b)-mu*(-nu*a-xi*b)),K*a,'same inverse row')
eq(nu*(lam*a-mu*b)+lam*(-nu*a-xi*b),-K*b,'same inverse row 2')
print(json.dumps({'status':'V42_ALGEBRA_PASS','identity_count':len(checks),'identities':checks}))
