#!/usr/bin/env python3
"""Exact symbolic identities for NEW prefix elimination and actual symmetry."""
import sympy as s
import json
count=0

def zero(x):
    global count
    assert s.cancel(s.expand(x))==0
    count+=1

k,r,ss,tt,A,B,c,d,p,e,be=s.symbols('k r s t A B c d p e beta',nonzero=True)
u=s.Matrix(s.symbols('u0:3'));x=s.Matrix(s.symbols('x0:3'));v=s.Matrix(s.symbols('v0:3'));q=s.Matrix(s.symbols('q0:3'))
D=s.Matrix([[k,A,B],[c*k,r+c*A,ss+c*B],[d*k,tt+d*A,-r+d*B]])
S=D+x*q.T;O=S+u*v.T
M=s.BlockMatrix([[s.Matrix([[1,-e],[be,p-e*be]]),s.Matrix.vstack(v.T,(q+be*v).T)],[s.Matrix.hstack(u,p*x-e*u),O]]).as_explicit()
J=s.Matrix([[0,-1],[1,0]]);Q=s.diag(s.eye(3),J)
# Exact actual matrix action, independent of numeric implementation.
Dk=s.diag(1,J)*D*s.diag(1,J)
expected=s.Matrix([[k,B,-A],[-d*k,r-d*B,tt+d*A],[c*k,ss+c*B,-r-c*A]])
for a in Dk-expected:zero(a)
uk=s.Matrix([u[0],-u[2],u[1]]);xk=s.Matrix([x[0],-x[2],x[1]])
vk=s.Matrix([v[0],v[2],-v[1]]);qk=s.Matrix([q[0],q[2],-q[1]])
Mk=s.BlockMatrix([[s.Matrix([[1,-e],[be,p-e*be]]),s.Matrix.vstack(vk.T,(qk+be*vk).T)],[s.Matrix.hstack(uk,p*xk-e*uk),Dk+xk*qk.T+uk*vk.T]]).as_explicit()
for a in Mk-Q*M*Q:zero(a)
H=D[1:,1:]-D[1:,0]*D[0,1:]/k
for a in H-s.Matrix([[r,ss],[tt,-r]]):zero(a)
Hk=Dk[1:,1:]-Dk[1:,0]*Dk[0,1:]/k
for a in Hk-s.Matrix([[r,tt],[ss,-r]]):zero(a)
zero(H.det()+r*(r+ss*tt/r))
# T = J0 M^T J0.
J0=s.diag(1,-1,1,1,1)
T=s.BlockMatrix([[s.Matrix([[1,-be],[e,p-be*e]]),s.Matrix.vstack(u.T,(-p*x+e*u).T)],[s.Matrix.hstack(v,-q-be*v),D.T+q*x.T+v*u.T]]).as_explicit()
for a in T-J0*M.T*J0:zero(a)
# Physical cap certificates use SAME e in both rows.
ai,aj,bi,bj=s.symbols('ai aj bi bj')
li=1-ai*p+bi*e;lj=1-aj*p+bj*e
zero(1+bi-ai*p-(li+bi*(1-e)))
zero(bi-bj-(aj*bi-ai*bj)*p-(bi*lj-bj*li))
# Reused tail monotonicity identity, not counted as new height theorem.
RR,SS,TT=s.symbols('R S T',positive=True)
zero(RR*r*((RR+SS*TT/RR)-(r+ss*tt/r))-((RR-r)*(RR*r-ss*tt)+r*tt*(SS-ss)+r*SS*(TT-tt)))
# Full determinant and 6-coordinate source replacement do not change first 3-tail formula.
zero(D.det()+k*(r*r+ss*tt))
print(json.dumps({'status':'V37_SYMBOLIC_IDENTITIES_PASS','exact_zero_identities':count}))
