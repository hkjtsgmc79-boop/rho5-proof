#!/usr/bin/env python3
"""Exact source for the target low-r interval. Inherited inequalities are explicit.
This model is a necessary relaxation, NOT a claimed completed height proof.
"""
from __future__ import annotations
from pathlib import Path
from itertools import product
from math import isqrt,gcd,lcm
import argparse,json
import sympy as s
R=s.Rational
ROOT_DEN=10**9

def sqrt_bounds(z):
    z=R(z);n=isqrt(int(s.floor(z*ROOT_DEN**2)))
    return R(n,ROOT_DEN),R(n if R(n*n,ROOT_DEN**2)==z else n+1,ROOT_DEN)
def make_model(K,J,typ,extra=True,norm_coupling=False):
    K,J=R(K),R(J);assert 2<K<=J<=R(43,20)
    k,r,w,A,B,c,d,p,e,be=s.symbols('k r w A B c d p e be')
    u=s.symbols('u0:3');x=s.symbols('x0:3');v=s.symbols('v0:3');q=s.symbols('q0:3');G=s.Symbol('G')
    vs=(k,r,w,A,B,c,d,p,e,be)+u+x+v+q+(G,)
    D=s.Matrix([[k,A,B],[c*k,r+c*A,r+c*B],[d*k,r+d*A,w+d*B]])
    rows=[]
    def add(label,expr):
        pp=s.Poly(s.expand(expr),*vs)
        if not pp.is_zero: rows.append((label,pp))
    def band(z,b,label):add(label+'+',b-z);add(label+'-',b+z)
    band(e,1,'e');band(be,1,'beta');band(p-e*be,1,'head')
    for i in range(3):
        band(u[i],1,f'u{i}');band(x[i],1,f'x{i}');band(v[i],1,f'v{i}');band(q[i],p,f'q{i}')
        band(p*x[i]-e*u[i],1,f'L{i}');band(q[i]+be*v[i],1,f'P{i}')
        for j in range(3):
            band(D[i,j],k,f'D{i}{j}');stage=D[i,j]+x[i]*q[j]
            band(stage,p,f'S{i}{j}');band(stage+u[i]*v[j],1,f'O{i}{j}')
    target=R(4132517,10**6)
    for lab,ex in [('F',r-w-target),('r+w',r+w),('low_r',k-r),('det3',4-p*k),('F4',4*p-r+w),
        ('head_parabola',p*(3-p)-k),('stage_pivots',3*p*k-k*k-p*r),('tail_pivots',2*k*r+k*w-r*r),
        ('cross1',2-k+(be-u[0])*v[0]),('cross2',2-k+(e-v[0])*u[0])]:add(lab,ex)
    add('b_ge_1',p*x[0]-1)
    if typ=='I':
        add('h_ge_1',-q[0]-1);add('fold_I',u[0]-v[0]);gactual=e*be;factors=(e,be)
        add('I_square_u',u[0]-u[0]**2-k+2);add('I_square_v',v[0]-v[0]**2-k+2)
        add('I_beta_u',be*u[0]-u[0]**2-be*(k-2));add('I_e_v',e*v[0]-v[0]**2-e*(k-2))
        add('beta_gt_u',be-u[0]);add('e_gt_v',e-v[0])
    elif typ=='II':
        add('h_le_1',1+q[0]);gactual=e*u[0];factors=(e,u[0])
        add('II_square_v',-v[0]-v[0]**2-k+2);add('II_u',u[0]-4*k+8)
        add('II_e_v',-e*v[0]-v[0]**2-e*(k-2));add('u_gt_beta',u[0]-be);add('e_gt_minus_v',e+v[0])
    else:raise ValueError(typ)
    add('G_def+',G-gactual);add('G_def-',gactual-G)
    add('G_head',G*(p+1-k)-(p-1)**2)
    add('G_ge_pminus1',G-p+1)
    for i,Y in enumerate(factors):
        add(f'G_factor_{i}',Y-G);add(f'factor_head_{i}',Y*(p+1-k)-(p-1)**2)
    for lam in map(R,[1,R(9,8),R(5,4),R(3,2),2,3,4,6,9]):
        add(f'G_tangent_{lam}',G-(2*lam-lam**2)*(p-1)-lam**2*(k-2))
    for layer,left,right,bound in [('uv',u[1:],v[1:],1),('xq',x[1:],q[1:],p),('core',(c,d),(A,B),k)]:
        for eps in product((-1,1),repeat=4):
            if eps[0]*eps[1]*eps[2]*eps[3]!=-1:continue
            add('CHSH_'+layer+'_'+''.join('p' if t==1 else 'm' for t in eps),2*bound-sum(eps[2*i+j]*left[i]*right[j] for i in range(2) for j in range(2)))
    if extra:
        g=4*(K-2)
        for i in (1,2):
            for j in (1,2):
                E=e*u[i];H=(be if typ=='I' else u[0])*v[j];T=u[i]*v[j]
                for sig in (-1,1):
                    add(f'anchor_sum_{i}{j}_{sig}',1-g+G+g*T+sig*(E+H))
                    add(f'anchor_diff_{i}{j}_{sig}',1-g+G-g*T+sig*(E-H))
                    add(f'plain_sum_{i}{j}_{sig}',2-G+T+sig*(E+H))
                    add(f'plain_diff_{i}{j}_{sig}',2-G-T+sig*(E-H))
    if norm_coupling:
        # Root-derived rational bounds, not unverified numerical p slices.
        g=4*(K-2); su,sv=sqrt_bounds(9-4*K)
        Lout=(1-sv)/2; Uout=(1+sv)/2
        lo16=R(int(s.floor(32*Lout)),32);hi16=R(int(s.ceiling(32*Uout)),32)
        blo=R(int(s.floor(32*(1-sv)/2)),32)
        def norm(z,lo,hi):
            assert lo<hi
            return (2*z-lo-hi)/(hi-lo)
        left=[norm(be,g if typ=='I' else blo,1),norm(u[0],lo16,hi16) if typ=='I' else norm(u[0],g,1),u[1],u[2]]
        right=[norm(e,g,1),norm(v[0],lo16,hi16) if typ=='I' else norm(v[0],-hi16,-lo16),v[1],v[2]]
        from itertools import combinations
        for ii in combinations(range(4),2):
            for jj in combinations(range(4),2):
                if ii==(2,3) or jj==(2,3):continue
                for ep in product((-1,1),repeat=4):
                    if ep[0]*ep[1]*ep[2]*ep[3]!=-1:continue
                    ex=2-sum(ep[2*i+j]*left[ii[i]]*right[jj[j]] for i in range(2) for j in range(2))
                    add('HEAD_NORM_'+str(ii)+str(jj)+str(ep),ex)
        xp=[2*x[0]-1,x[1],x[2]];qp=[2*q[0]+p,q[1],q[2]]
        for ii in ((0,1),(0,2)):
            for jj in ((0,1),(0,2)):
                for ep in product((-1,1),repeat=4):
                    if ep[0]*ep[1]*ep[2]*ep[3]!=-1:continue
                    add('STAGE_HEAD_NORM_'+str(ii)+str(jj)+str(ep),2*p-sum(ep[2*i+j]*xp[ii[i]]*qp[jj[j]] for i in range(2) for j in range(2)))
    rootlow,rootup=sqrt_bounds(9-4*K)
    ell=max((3-rootup)/2,target/4,K/2);P=min((3+rootup)/2,4/K)
    L=(1-rootup)/2;U=(1+rootup)/2;g=4*(K-2)
    xl= max(K/P-1,1/P)
    if typ=='I':xl=max(xl,(K-1+sqrt_bounds(K*(K-2))[0])/2)
    lower=[K,target/2,-J,-J,-J,-1,-1,ell,ell-1,ell-1,L if typ=='I' else g,-1,-1,xl,-1,-1,L if typ=='I' else -U,-1,-1,-P if typ=='I' else -1,-P,-P,g]
    upper=[J,J,J-target,0,J,1,1,P,1,1,U if typ=='I' else 1,1,1,1,1,1,U if typ=='I' else -L,1,1,-1 if typ=='I' else P-K,P,P,1]
    lo=[int(s.floor(z*ROOT_DEN)) for z in lower];hi=[int(s.ceiling(z*ROOT_DEN)) for z in upper]
    assert all(a<b for a,b in zip(lo,hi))
    monos=sorted({m for _,pp in rows for m,_ in pp.terms() if sum(m)==2})
    pairs=[[i for i,a in enumerate(m) for _ in range(a)] for m in monos]
    pos={m:len(vs)+i for i,m in enumerate(monos)}
    out=[]
    for lab,pp in rows:
        co=[s.S(0)]*(len(vs)+len(monos));rhs=s.S(0)
        for mon,val in pp.terms():
            deg=sum(mon)
            if deg==0:rhs=val
            elif deg==1:co[mon.index(1)]=-val
            elif deg==2:co[pos[mon]]=-val
            else:raise ValueError((lab,mon))
        den=lcm(*[int(t.q) for t in co+[rhs]])
        vals=[int(t*den) for t in co+[rhs]];gg=gcd(*vals)
        vals=[t//gg for t in vals]
        assert max(map(abs,vals))<2**62
        out.append({'name':lab,'coefficients':vals[:-1],'rhs':vals[-1],'polynomial':str(pp.as_expr()),'positive_scale':str(R(den,gg))})
    return {'variables':list(map(str,vs)),'target':str(target),'K':str(K),'J':str(J),'type':typ,'low_r':True,'fold_I':typ=='I','extra_anchor':extra,'norm_coupling':norm_coupling,'root_denominator':ROOT_DEN,'root_numerators':[lo,hi],'pairs':pairs,'rows':out}

def headers(data,path):
    path=Path(path);path.mkdir(exist_ok=True,parents=True)
    nv=len(data['variables']);nn=nv+len(data['pairs']);nr=len(data['rows'])
    cpp=lambda a:'{'+','.join(cpp(x) if isinstance(x,(list,tuple)) else str(x) for x in a)+'}'
    exact=['#pragma once','#include <vector>','#include <utility>',f'constexpr int EV={nv}, EN={nn}, EB={nr};',f'constexpr long long ROOT_DEN={data["root_denominator"]};',
        'inline const std::vector<std::pair<int,int>> epairs='+cpp(data['pairs'])+';',
        'inline const std::vector<std::vector<long long>> ebase='+cpp([r['coefficients'] for r in data['rows']])+';',
        'inline const std::vector<long long> erhs='+cpp([r['rhs'] for r in data['rows']])+';',
        'inline const std::vector<long long> erootlo='+cpp(data['root_numerators'][0])+';',
        'inline const std::vector<long long> eroothi='+cpp(data['root_numerators'][1])+';']
    (path/'mc_exact_model.hpp').write_text('\n'.join(exact)+'\n')
    (path/'mc_model.hpp').write_text('#pragma once\n#include "mc_exact_model.hpp"\nconstexpr int NV=EV,NX=EN;\nconst auto &pairs=epairs;\ninline const std::vector<std::vector<double>> base=[](){std::vector<std::vector<double>> a;for(auto&r:ebase)a.emplace_back(r.begin(),r.end());return a;}();\ninline const std::vector<double> rhs(erhs.begin(),erhs.end());\n')
    (path/'model.json').write_text(json.dumps(data,indent=2)+'\n')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--K',default='107/50');ap.add_argument('--J',default='43/20');ap.add_argument('--type',choices=['I','II'],required=True);ap.add_argument('--out',required=True);ap.add_argument('--no-extra',action='store_true');ap.add_argument('--norm-coupling',action='store_true');a=ap.parse_args()
    data=make_model(a.K,a.J,a.type,not a.no_extra,a.norm_coupling);headers(data,a.out)
    print(json.dumps({k:data[k] for k in ['K','J','type','target']}), 'vars',len(data['variables']),'products',len(data['pairs']),'rows',len(data['rows']))
