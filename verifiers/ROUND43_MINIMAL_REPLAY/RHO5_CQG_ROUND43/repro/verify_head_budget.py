#!/usr/bin/env python3
"""Exact lightweight audit; run on X as part of the parent line's checks.

Usage: python verify_head_budget.py [--v32-zip PATH] [--grid]
No floating point optimizer and no full-domain computational claim.
"""
import argparse
import json
import zipfile
from itertools import product
from fractions import Fraction as Q
import sympy as sp


def verify_identities():
    p, e, beta, b, h, u, v, S = sp.symbols("p e beta b h u v S")
    O = S + u*v
    k = S + b*h/p
    delta = p*(3-p)-k
    t, z, g = p-b, p-h, e*beta
    rhs1 = (1-O) + (u*v-(b-1)*(h-1)/g)
    rhs1 += (1-g)*(b-1)*(h-1)/g + (2-p)*(t+z)+(p-1)*t*z/p
    rhs2 = (p-1)*(beta-p+1)+(1-beta)*(p-S)+(1-h+beta*v)
    rhs2 += beta*(1-O)+beta*(1-u)*(-v)+(1-b/p)*h
    rhs3 = (p-1)*(e-p+1)+(1-e)*(p-S)+(1-b+e*u)
    rhs3 += e*(1-O)+e*(1-v)*(-u)+(1-h/p)*b
    rhs4 = (p-1)*(e-p+1)/p+(1-e/p)*(p-S)
    rhs4 += (1-b-e*(S-1))/p+(1-h)*b/p
    a0,b0,Hroot = sp.symbols("a0 b0 Hroot")
    R1,R2 = e*u-b+1,beta*v-h+1
    loss_I = 1-O+a0*(R1+R2)+a0*a0*(1-e*beta)+(2-Hroot)*(2*p-b-h)
    gap_I = (v/e-a0)*R1+((b-1)/(e*beta)-a0)*R2
    gap_I += ((b-1)*(h-1)/(e*beta)-a0*a0)*(1-e*beta)
    gap_I += (Hroot-p)*(2*p-b-h)+(p-1)*(p-b)*(p-h)/p
    loss_II = (p-1)*(beta-p+1)+(1-h+beta*v)
    loss_II += b0*(1-O+u*v-v)+(1-b/p)*h
    gap_II = (1-beta)*(p-S)+(beta-b0)*((1-O)+(1-u)*(-v))
    loss_III = (p-1)*(e-p+1)+(1-b+e*u)
    loss_III += b0*(1-O+u*v-u)+(1-h/p)*b
    gap_III = (1-e)*(p-S)+(e-b0)*((1-O)+(1-v)*(-u))
    rect_R = 2+(u-beta)*(-v)-k
    rect_L = 2+(v-e)*(-u)-k
    r, w = sp.symbols("r w")
    rows = {"case_I": delta-rhs1, "case_II": delta-rhs2,
            "case_III": delta-rhs3, "case_IV": 2-k-rhs4,
            "case_I_receiver_split": u*v-(b-1)*(h-1)/g
              -((e*u-b+1)*beta*v+(b-1)*(beta*v-h+1))/g,
            "parabola": p*(3-p) - (sp.Rational(9,4)-(p-sp.Rational(3,2))**2),
            "middle_window_quadratic": p*(k*(3-k/p)-r)-(3*p*k-k*k-p*r),
            "last_window_quadratic": k*(r*(3-r/k)-(r-w))-(2*k*r+k*w-r*r)}
    rows.update({
        "loss_I_nonnegative_remainder": delta-loss_I-gap_I,
        "loss_II_nonnegative_remainder": delta-loss_II-gap_II,
        "loss_III_nonnegative_remainder": delta-loss_III-gap_III,
        "receiver_rectangle_R_all_cases": rect_R-((1-O)+(1-h+beta*v)+(1-b/p)*h),
        "receiver_rectangle_L_all_cases": rect_L-((1-O)+(1-b+e*u)+(1-h/p)*b),
        "case_II_opposite_head_root":
          e*delta-(1-e)*(p-1)**2
          -(e*(delta-(p-1)*(beta-p+1))+(p-1)*(e*beta-p+1)),
        "case_III_opposite_head_root":
          beta*delta-(1-beta)*(p-1)**2
          -(beta*(delta-(p-1)*(e-p+1))+(p-1)*(e*beta-p+1)),
        "case_I_beta_gap": beta-u-k+2-((beta-u)*(1-v)+rect_R),
        "case_I_e_gap": e-v-k+2-((e-v)*(1-u)+rect_L),
        "case_II_u_gap": u-beta-k+2-((u-beta)*(1+v)+rect_R),
        "case_III_v_gap": v-e-k+2-((v-e)*(1+u)+rect_L),
    })
    for name, expr in rows.items():
        assert sp.cancel(expr) == 0, (name, sp.factor(expr))
    x,qq,kk = sp.symbols('x qq kk')
    sub = {b:p*x,h:-qq,S:kk+x*qq}
    actual_vars = (p,e,beta,u,v,x,qq,kk)
    for name,expr in [('loss_I',delta-loss_I),('loss_II',delta-loss_II),
                      ('loss_III',delta-loss_III),('rectangle_R',rect_R),('rectangle_L',rect_L)]:
        exact_actual = sp.cancel(expr.subs(sub,simultaneous=True))
        assert sp.Poly(exact_actual,*actual_vars).total_degree() <= 2, name
    return list(rows)


def pivots_with_cp(matrix):
    a = [[Q(x) for x in row] for row in matrix]
    pivots = []
    for i in range(len(a)):
        p = a[i][i]
        assert p != 0
        assert abs(p) == max(abs(a[r][c]) for r in range(i,len(a))
                             for c in range(i,len(a))), (i,a,p)
        pivots.append(p)
        for r in range(i+1,len(a)):
            for c in range(i+1,len(a)):
                a[r][c] -= a[r][i]*a[i][c]/p
    return pivots


def verify_equality_heads():
    half = Q(1,2)
    heads = [
        [[1,-1,half],[1,half,-1],[half,1,1]],
        [[1,-1,-half],[half,1,-1],[1,half,1]],
        [[1,-half,1],[1,1,-half],[-half,1,1]],
    ]
    expected = [Q(1),Q(3,2),Q(9,4)]
    for matrix in heads:
        assert pivots_with_cp(matrix) == expected
        B = sp.Matrix([[sp.Rational(x.numerator,x.denominator) if isinstance(x,Q)
                        else x for x in row] for row in matrix])
        assert B.T*B == sp.Rational(9,4)*sp.eye(3)
    return len(heads)


def verify_endpoint_cross_budget():
    """A complete small vertex table proves a continuous multilinear outer bound."""
    pairs = [(2,-2),(2,1),(1,2),(-2,2),(-2,-1),(-1,-2)]
    def vertices(i,j,sgn):
        remaining = 3-i-j
        result = []
        for (a,b),c in product(pairs,[-2,2]):
            v = [0,0,0]
            v[i],v[j],v[remaining] = a,sgn*b,c
            result.append(v)
        return result
    cases = [
       ([[2,-2,1],[2,1,-2],[1,2,2]],(0,1,1),(1,0,-1)),
       ([[2,-2,-1],[1,2,-2],[2,1,2]],(0,1,1),(2,0,-1)),
       ([[2,-1,2],[2,2,-1],[-1,2,2]],(2,0,-1),(1,0,-1)),
    ]
    result = []
    for B_twice, p_spec, q_spec in cases:
        N = list(map(list,zip(*B_twice)))
        P, C = vertices(*p_spec),vertices(*q_spec)
        def support(vector):
            return max(sum(a[i]*N[i][j]*vector[j]
                           for i in range(3) for j in range(3)) for a in P)
        maximum = max(support([c[i]+d[i] for i in range(3)])
                    + support([c[i]-d[i] for i in range(3)])
                      for c,d in product(C,repeat=2))
        assert maximum == 84
        result.append({"row_vertices":len(P),"column_vertices":len(C),
                       "integer_maximum":maximum,"scale":18,
                       "continuous_CHSH_outer_maximum":str(Q(maximum,18))})
    return result


def verify_v32(path):
    with zipfile.ZipFile(path) as z:
        matches = [n for n in z.namelist() if n.endswith('/strict_witness.json')]
        assert len(matches) == 1
        data = json.loads(z.read(matches[0]))
    matrix = [[Q(x) for x in row] for row in data['matrix']]
    piv = pivots_with_cp(matrix)
    p, k = piv[1:3]
    assert p*(3-p)-k > 0
    return {"p": str(p), "k": str(k), "positive_parabolic_defect": str(p*(3-p)-k)}


def verify_projection_grid():
    """Finite exact error-finding check, explicitly NOT a continuum proof."""
    count = 0
    for p in [Q(i,8) for i in range(9,17)]:
        for e in [Q(i,8) for i in range(1,9)]:
            for beta in [Q(i,8) for i in range(1,9)]:
                if e*beta < p-1:
                    continue
                for b in [p*Q(i,8) for i in range(9)]:
                    for h in [p*Q(i,8) for i in range(9)]:
                        aa = max(Q(-1),(b-1)/e)
                        cc = max(Q(-1),(h-1)/beta)
                        if aa > 1 or cc > 1:
                            continue
                        m = min(Q(1),aa,cc,aa*cc)
                        upper = min(p,1-m)+b*h/p
                        assert upper <= p*(3-p), (p,e,beta,b,h,upper)
                        count += 1
    return {"finite_exact_projection_points": count,
            "scope": "finite error-finding only; not a proof of global coverage"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--v32-zip')
    ap.add_argument('--grid',action='store_true')
    args = ap.parse_args()
    result = {"identities": verify_identities(),
              "equality_heads_with_exact_cp": verify_equality_heads(),
              "endpoint_cross_budget": verify_endpoint_cross_budget()}
    if args.v32_zip:
        result['v32'] = verify_v32(args.v32_zip)
    if args.grid:
        result['grid'] = verify_projection_grid()
    result['status'] = 'HEAD_PIVOT_PARABOLA_EXACT_AUDIT_PASS'
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__ == '__main__':
    main()
