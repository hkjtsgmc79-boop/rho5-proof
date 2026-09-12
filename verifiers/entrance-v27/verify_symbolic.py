"""Exact algebra checks for V27; no inequalities are inferred from sampling."""
import json
from pathlib import Path
import sympy as S

names=[]
def check(name, expr):
    assert S.cancel(S.expand(expr)) == 0, name
    names.append(name)

be,e,p,U,V,T,X,Y,Z,v0,v1,v2,q0,q1,q2,A,B,C,D=S.symbols(
    'be e p U V T X Y Z v0 v1 v2 q0 q1 q2 A B C D')

def L(be,U,V,T,X,Y,Z,A,B,D):
    return [be*U*X,be*V*Y,be*T*Z,V*T,V*(V-be*Y),V*(be*Z-T),
            be*U*V*(U*Y-X*V),-U*V*A,-U*V*B,-U*V*D]

def R(e,p,v0,v1,v2,q0,q1,q2,A,B,C,D):
    return [-e*v0*q0,-e*v1*q1,-e*v2*q2,v1*v2,
            v1*(p*v1+e*q1),v1*(-e*q2-p*v2),
            -e*v0*v1*(v0*q1-q0*v1),-v0*v1*C,-v0*v1*D,-v0*v1*B]

def cof(be,U,V,T,X,Y,Z):
    return [U-be*X,V-be*Y,be*Z-T,U*Y-X*V,U*Z-T*X,V*Z-T*Y]

ll=L(be,U,V,T,X,Y,Z,A,B,D)
rr=R(e,p,v0,v1,v2,q0,q1,q2,A,B,C,D)
cc=cof(be,U,V,T,X,Y,Z)
for alpha in (-1,1):
    for theta in (-1,1):
        for eta in (-1,1):
            key=f'{alpha}_{theta}_{eta}'
            lm=L(alpha*be,theta*eta*U,theta*V,theta*T,
                 alpha*theta*eta*X,alpha*theta*Y,alpha*theta*Z,
                 eta*A,eta*B,eta*D)
            rm=R(alpha*e,p,theta*eta*v0,theta*v1,theta*v2,
                 alpha*theta*eta*q0,alpha*theta*q1,alpha*theta*q2,
                 eta*A,eta*B,eta*C,eta*D)
            cm=cof(alpha*be,theta*eta*U,theta*V,theta*T,
                   alpha*theta*eta*X,alpha*theta*Y,alpha*theta*Z)
            factors=[theta*eta,theta,theta,alpha*eta,alpha*eta,alpha]
            for i in range(10):
                check(f'left_gauge_{key}_{i+1}',lm[i]-ll[i])
                check(f'right_gauge_{key}_{i+1}',rm[i]-rr[i])
            for i in range(6):
                check(f'cofactor_gauge_{key}_{i+1}',cm[i]-factors[i]*cc[i])

lt=L(-e,v0,v1,v2,q0/p,q1/p,q2/p,C,D,B)
for i in range(10):
    factor=p if i in (0,1,2,4,5,6) else 1
    check(f'transpose_gate_{i+1}',factor*lt[i]-rr[i])

check('adjacent_delta',Y*cc[0]-(cc[3]+X*cc[1]))
check('adjacent_mu',cc[5]-(Z*cc[1]+Y*cc[2]))
check('adjacent_Delta',Y*cc[4]-(Z*cc[3]+X*cc[5]))

# One general-index identity proves the diagonal covariance of each
# scalar Schur-complement entry; induction gives all stages.
a00,ai0,a0j,aij,d0,di,dj=S.symbols('a00 ai0 a0j aij d0 di dj')
check('diagonal_Schur_covariance',
      di*dj*aij-(di*d0*ai0)*(d0*dj*a0j)/(d0*d0*a00)
      -di*dj*(aij-ai0*a0j/a00))

# Native transposition, including both unequal p factors.
check('transpose_head',p-(-be)*(-e)-(p-e*be))
check('transpose_left_second',p*(q0/p)-(-be)*v0-(be*v0+q0))
check('transpose_right_second',(-e)*U+p*X-(p*X-e*U))
check('transpose_bottom_correction',(q0/p)*(p*X)+v0*U-(X*q0+U*v0))

# Ordered-ray determinant is positive from positive masses and ordered t.
m,n,t,u=S.symbols('m n t u')
check('ordered_ray_determinant',(m*t)*(n*(1-u))-(m*(1-t))*(n*u)-m*n*(t-u))

# Exact contraction of the left cofactors.
a,b,c=S.symbols('scale_a scale_b scale_c', nonzero=True)
scaled=cof(a*be,b*U,c*V,c*T,b*X/a,c*Y/a,c*Z/a)
factors=[b,c,c,b*c/a,b*c/a,c*c/a]
for i in range(6):
    check(f'contraction_cofactor_{i+1}',scaled[i]-factors[i]*cc[i])

out={'status':'PASS','symbolic_identities':len(names),'checks':names,
     'scope':'algebraic dictionaries only; no remaining-sign-domain exclusion'}
Path('symbolic_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='checks'}))
