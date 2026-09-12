"""Exact bounded identity audit for X; not an infeasibility search."""
from itertools import product
from pathlib import Path
import argparse
import importlib.util
import json
import sympy as s
from head_anchor_tail_link import (anchor_tail_expressions,
    anchor_tail_projected_rows,head_anchor_tail_lift)


def mc_pass(a,b,z,la,ua,lb,ub):
    return (z>=la*b+lb*a-la*lb and z>=ua*b+ub*a-ua*ub
            and z<=ua*b+lb*a-ua*lb and z<=la*b+ub*a-la*ub)


def pairs(rows):
    return {tuple(str(poly.gens[i]) for i,p in enumerate(m) for _ in range(p))
            for _,poly in rows for m,_ in poly.terms() if sum(m)==2}


def run(builder):
    spec=importlib.util.spec_from_file_location('r44_anchor_base',builder)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    records=[]
    g=s.Rational(3,5)
    for case in ('I','II','III'):
        vs0,_,rows0,lo0,hi0,_=mod.model(s.Rational(43,20),case,True)
        G=s.Symbol('G');vs=tuple(vs0)+(G,)
        _,source,E,H,T=anchor_tail_expressions(vs,case)
        rows=[(name,s.Poly(poly.as_expr(),*vs)) for name,poly in rows0]
        rows.extend([('actual_G+',s.Poly(G-source,*vs)),
                     ('actual_G-',s.Poly(source-G,*vs))])
        lo=list(lo0)+[g];hi=list(hi0)+[s.Integer(1)]
        direct=anchor_tail_projected_rows(vs,case,g)
        both=anchor_tail_projected_rows(vs,case,g,include_plain=True)
        assert len(direct)==16 and len(both)==32
        assert pairs(direct)<=pairs(rows)
        for i in (1,2):
            for j in (1,2):
                Ee,Hh,Tt=E[i-1],H[j-1],T[i,j]
                assert s.expand(Ee*Hh-source*Tt)==0
                for sign in (-1,1):
                    targets=(1-g+G+g*Tt+sign*(Ee+Hh),
                             1-g+G-g*Tt+sign*(Ee-Hh),
                             2-G+Tt+sign*(Ee+Hh),
                             2-G-Tt+sign*(Ee-Hh))
                    proofs=((1+sign*Ee)*(1+sign*Hh)+(G-g)*(1-Tt),
                            (1+sign*Ee)*(1-sign*Hh)+(G-g)*(1+Tt),
                            (1+sign*Ee)*(1+sign*Hh)+(1-G)*(1+Tt),
                            (1+sign*Ee)*(1-sign*Hh)+(1-G)*(1-Tt))
                    for target,proof in zip(targets,proofs):
                        assert s.expand((target-proof).subs(G,source))==0
        nv,nr,nlo,nhi,manifest=head_anchor_tail_lift(vs,rows,lo,hi,head_case=case)
        assert len(nv)-len(vs)==4 and len(nr)-len(rows)==24
        assert len(pairs(nr)-pairs(rows))==4
        assert all(poly.total_degree()<=2 for _,poly in nr)
        assert all(l<=h for l,h in zip(nlo,nhi))
        records.append(dict(head_case=case,direct_rows=16,direct_added_products=0,
                            optional_lift=manifest))
    # Exact +1 combinations between abstract scalar envelopes and E*H MC.
    Ge,Ee,Hh,Tt,Z,gg=s.symbols('Ge Ee Hh Tt Z gg')
    C1=Z+Ge-gg*Tt-gg;C2=1-Ge-Tt+Z
    C3=1-Ge+Tt-Z;C4=Ge-gg+gg*Tt-Z
    for sign in (-1,1):
        Ms=1+sign*Ee+sign*Hh+Z
        Md=1+sign*Ee-sign*Hh-Z
        assert s.expand(Ms+C4-(1-gg+Ge+gg*Tt+sign*(Ee+Hh)))==0
        assert s.expand(Md+C1-(1-gg+Ge-gg*Tt+sign*(Ee-Hh)))==0
        assert s.expand(Ms+C3-(2-Ge+Tt+sign*(Ee+Hh)))==0
        assert s.expand(Md+C2-(2-Ge-Tt+sign*(Ee-Hh)))==0
    # Local strict-strengthening witness; not a complete X point.
    e=be=s.Rational(4,5);u=v=s.Rational(1,2)
    Gv=s.Rational(3,5);Ev=Hv=s.Rational(11,20);Tv=0
    assert mc_pass(e,be,Gv,0,1,0,1)
    assert mc_pass(e,u,Ev,0,1,-1,1)
    assert mc_pass(be,v,Hv,0,1,-1,1)
    assert mc_pass(u,v,Tv,-1,1,-1,1)
    rectangle=(4*Gv-2*e-2*be+1,2*Hv-v,2*Ev-u,Tv)
    for signs in product((-1,1),repeat=4):
        if signs[0]*signs[1]*signs[2]*signs[3]==-1:
            assert 2-sum(a*b for a,b in zip(signs,rectangle))>=0
    assert 1-g+Gv+g*Tv-Ev-Hv==-s.Rational(1,10)
    p,k=s.symbols('p k')
    assert s.expand((p-1)**2-4*(k-2)*(p+1-k)-(p-2*k+3)**2)==0
    return dict(status='R44_HEAD_ANCHOR_PROJECTED_TAIL_EXACT_IDENTITY_PASS',
                scope='Identity, positive-combination and local relaxation audit only',
                root_obligation='g and G source equality require caller-certified roots/model',
                strict_local_gap='-1/10',records=records)


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--builder',type=Path,required=True)
    ap.add_argument('--output',type=Path);args=ap.parse_args()
    report=json.dumps(run(args.builder),indent=2)+'\n'
    if args.output:args.output.write_text(report)
    print(report,end='')
