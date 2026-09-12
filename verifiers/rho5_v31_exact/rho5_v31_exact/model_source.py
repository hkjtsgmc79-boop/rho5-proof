"""V31 exact quadratic source. No numerical solver or old certificate is used.

The only imported mathematical upper bound is rho_4(real)=4, used as F<=4p.
All other guards have elementary same-state derivations in THEOREM.md.
"""
from __future__ import annotations
import sympy as s


def make_model():
    k,r,w,A,B,c,d,p,e,be=s.symbols('k r w A B c d p e be')
    u=s.symbols('u0:3'); x=s.symbols('x0:3'); v=s.symbols('v0:3'); q=s.symbols('q0:3')
    vs=(k,r,w,A,B,c,d,p,e,be)+u+x+v+q
    D=s.Matrix([[k,A,B],[c*k,r+c*A,r+c*B],[d*k,r+d*A,w+d*B]])
    rows=[]
    def band(value,bound,label):
        rows.extend([(label+'+',bound-value),(label+'-',bound+value)])
    band(e,1,'e');band(be,1,'beta');band(p-e*be,1,'head')
    for i in range(3):
        band(u[i],1,'u'+str(i));band(x[i],1,'x'+str(i))
        band(v[i],1,'v'+str(i));band(q[i],p,'q'+str(i))
        band(p*x[i]-e*u[i],1,'L'+str(i));band(q[i]+be*v[i],1,'P'+str(i))
        for j in range(3):
            band(D[i,j],k,f'D{i}{j}')
            stage=D[i,j]+x[i]*q[j]
            band(stage,p,f'S{i}{j}');band(stage+u[i]*v[j],1,f'O{i}{j}')
    f=s.Rational(1653,400);eta=f/2-2
    rows.extend([
        ('F',r-w-f),('Fcore',9*k/4-r+w),('r+w',r+w),
        ('det3',4-p*k),('plower',4*p-r+w),
        ('rAd',k*(1+d)-r),('rBc',k-B-r),('rAc',k-A-r),
        ('B-A',B-A-r+w+2*k),('B',2*k-r+w-B),('cd',c-d-eta)
    ])
    rows=[(name,s.Poly(expr,*vs)) for name,expr in rows if expr!=0]
    lower=[4*f/9,f/2,-2,-2,-2,2*eta,eta,f/4,f/4-1,f/4-1,
           0,-1,-1,-1,-1,-1,-1,-1,-1,-2,-2,-2]
    upper=[2,4-eta,-eta,-2*eta,-2*eta,1,1-eta,2,1,1,
           1,1,1,1,1,1,1,1,1,2,2,2]
    return vs,D,rows,list(map(s.Rational,lower)),list(map(s.Rational,upper))


def export_payload():
    vs,D,rows,lower,upper=make_model();nv=len(vs)
    monomials=sorted({mon for _,poly in rows for mon,_ in poly.terms() if sum(mon)==2})
    pairs=[]
    for mon in monomials:
        indices=[i for i,power in enumerate(mon) for _ in range(power)]
        pairs.append(indices)
    positions={mon:nv+i for i,mon in enumerate(monomials)}
    output=[]
    for name,poly in rows:
        coefficients=[s.Rational(0)]*(nv+len(pairs));rhs=s.Rational(0)
        for mon,value in poly.terms():
            degree=sum(mon)
            if degree==0:rhs=value
            elif degree==1:coefficients[mon.index(1)]=-value
            elif degree==2:coefficients[positions[mon]]=-value
            else:raise AssertionError('Source must remain quadratic')
        integers=[1600*t for t in coefficients]+[1600*rhs]
        if not all(t.q==1 for t in integers):raise AssertionError('Nonintegral scaled row')
        output.append(dict(name=name,coefficients=list(map(int,integers[:-1])),rhs=int(integers[-1]),polynomial=str(poly.as_expr())))
    root=[[int(4800*t) for t in a] for a in (lower,upper)]
    if any(4800*t != int(4800*t) for a in (lower,upper) for t in a):raise AssertionError('Root denominator')
    return dict(variables=list(map(str,vs)),target='1653/400',base_multiplier=1600,
                root_denominator=4800,root_numerators=root,pairs=pairs,rows=output)


def cpp_header(data):
    nv=len(data['variables']);n=nv+len(data['pairs']);rows=data['rows'];roots=data['root_numerators']
    lines=['#pragma once','#include <vector>','#include <utility>',f'constexpr int EV={nv}, EN={n}, EB={len(rows)};',
        'inline const std::vector<std::pair<int,int>> epairs={'+','.join('{%s,%s}'%(i,j) for i,j in data['pairs'])+'};',
        'inline const std::vector<std::vector<long long>> ebase={'+','.join('{'+','.join(map(str,r['coefficients']))+'}' for r in rows)+'};',
        'inline const std::vector<long long> erhs={'+','.join(str(r['rhs']) for r in rows)+'};',
        'inline const std::vector<long long> erootlo={'+','.join(map(str,roots[0]))+'};',
        'inline const std::vector<long long> eroothi={'+','.join(map(str,roots[1]))+'};']
    return '\n'.join(lines)+'\n'
