#!/usr/bin/env python3
"""Independently rebuild source, lift semantics, core identities and determinant cap."""
from __future__ import annotations
import itertools,json,sys
from fractions import Fraction as Q
from pathlib import Path
import sympy as s
from model_source import make_model,export_payload,cpp_header
ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:raise AssertionError(message)

def det3(m):
    return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])
           -m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
           +m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))

def main(model_path=None):
    data=json.loads((Path(model_path) if model_path else ROOT/'mc_exact_model.json').read_text())
    expected=export_payload();require(data==expected,'symbolic source/JSON mismatch')
    require((ROOT/'mc_exact_model.hpp').read_text()==cpp_header(expected),'C++ dictionary mismatch')
    vs,D,rows,lo,hi=make_model();k,r,w,A,B,c,d,p,e,be=vs[:10]
    u=s.Matrix(vs[10:13]);x=s.Matrix(vs[13:16]);v=s.Matrix(vs[16:19]);q=s.Matrix(vs[19:22])
    O=D+x*q.T+u*v.T
    M=s.Matrix([[1,-e,*v],[be,p-e*be,*(q+be*v)] ]+
               [[u[i],p*x[i]-e*u[i],*list(O.row(i))] for i in range(3)])
    count=0
    def zero(expr,label):
        nonlocal count
        require(s.cancel(expr)==0,label);count+=1
    block1=M[1:,1:]-M[1:,:1]*M[:1,1:]
    expected1=s.Matrix([[p,*q]]+[[p*x[i],*list((D+x*q.T).row(i))] for i in range(3)])
    for i in range(4):
        for j in range(4):zero(block1[i,j]-expected1[i,j],f'first Schur {i},{j}')
    block2=block1[1:,1:]-block1[1:,:1]*block1[:1,1:]/p
    for i in range(3):
        for j in range(3):zero(block2[i,j]-D[i,j],f'second Schur {i},{j}')
    H=D[1:,1:]-D[1:,:1]*D[:1,1:]/k
    for i in range(2):
        for j in range(2):zero(H[i,j]-([r,r,r,w][2*i+j]),f'third Schur {i},{j}')
    zero(H[1,1]-H[1,0]*H[0,1]/r-(w-r),'last pivot')
    zero(M[:3,:3].det()-p*k,'same leading minor p*k')
    aa,bb,cc,dd,z,ww=s.symbols('a b c d z omega')
    left=aa*cc*(s.Rational(9,4)-(1+z-ww))
    right=(aa*cc*(z-s.Rational(1,2))**2+(bb*cc-z)*aa*dd+z*(aa*dd-z)
           +z**2*(1-aa*cc)+aa*cc*(1+ww-bb*dd))
    zero(left-right,'9/4 core nonnegative decomposition')
    F=r-w
    zero((c-d)*(-B)-(F-2*k)-((k-D[1,2])+(k+D[2,2])),'first joint gap')
    zero(d*(B-A)-(F-2*k)-((k-D[2,1])+(k+D[2,2])),'second joint gap')
    zero(k*(1+d)-r-((k-D[2,1])+d*(k+A)),'rAd')
    zero(k-B-r-((k-D[1,2])+(1-c)*(-B)),'rBc')
    zero(k-A-r-((k-D[1,1])+(1-c)*(-A)),'rAc')
    vals=[]
    for signs in itertools.product((-1,1),repeat=9):
        mat=[signs[0:3],signs[3:6],signs[6:9]];vals.append(abs(det3(mat)))
    require(max(vals)==4,'unit 3x3 determinant vertex cap')
    require(len(rows)==106 and len(data['pairs'])==35,'model counts')
    require(all(t>0 for t in (lo[0],lo[1],lo[7],lo[8],lo[9])),'positive root denominators')
    require(Q(1653,400)<Q(4132517,1000000),'rational safety threshold vs alpha lower endpoint')
    print(json.dumps(dict(status='V31_MODEL_AND_CORE_IDENTITIES_PASS',rows=len(rows),products=len(data['pairs']),
                          symbolic_identities=count,determinant_vertices=len(vals),rho4='IMPORTED_CLASSICAL_REAL_CP_BOUND_4')))
if __name__=='__main__':main(sys.argv[1] if len(sys.argv)>1 else None)
