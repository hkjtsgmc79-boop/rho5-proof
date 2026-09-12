"""Exact dictionaries for RHO5 V27.  All arithmetic is rational.

This module verifies identities and explicit witnesses.  It is NOT an
exclusion certificate for the remaining high-value sign chambers.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
from typing import Sequence


def req(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def rat(x):
    if isinstance(x, (float, bool)):
        raise TypeError('Use exact integers, strings, or Fraction values')
    return Q(x)


def transpose(M):
    return [list(row) for row in zip(*M)]


def build(*, p, k, r, w, e, beta, u, x, vv, qq, A, B, c, d):
    """Signed X-chart: A=D01, B=D02, c=D10/k, d=D20/k."""
    D = [[k, A, B], [c*k, c*A+r, c*B+r],
         [d*k, d*A+r, d*B+w]]
    P = [beta*vv[j]+qq[j] for j in range(3)]
    L = [p*x[i]-e*u[i] for i in range(3)]
    O = [[D[i][j]+x[i]*qq[j]+u[i]*vv[j] for j in range(3)] for i in range(3)]
    return [[Q(1), -e, *vv], [beta, p-e*beta, *P]] + [
        [u[i], L[i], *O[i]] for i in range(3)]


def extract(M):
    req(len(M) == 5 and all(len(row) == 5 for row in M), '5 by 5')
    req(M[0][0] == 1, 'First pivot must be normalized to +1')
    e, beta = -M[0][1], M[1][0]
    p = M[1][1]+e*beta
    req(p > 0, 'Positive second pivot')
    u, vv = [M[i+2][0] for i in range(3)], list(M[0][2:])
    x = [(M[i+2][1]+e*u[i])/p for i in range(3)]
    qq = [M[1][j+2]-beta*vv[j] for j in range(3)]
    D = [[M[i+2][j+2]-x[i]*qq[j]-u[i]*vv[j] for j in range(3)] for i in range(3)]
    k = D[0][0]
    req(k > 0, 'Positive third pivot')
    A, B, c, d = D[0][1], D[0][2], D[1][0]/k, D[2][0]/k
    r, w = D[1][1]-c*A, D[2][2]-d*B
    req(r > 0 and D[1][2]-c*B == r and D[2][1]-d*A == r,
        'Normalized signed X-chart')
    return dict(p=p,k=k,r=r,w=w,e=e,beta=beta,u=u,x=x,vv=vv,qq=qq,
                A=A,B=B,c=c,d=d,D=D,F=r-w)


def rebuild(s, **updates):
    names = ('p','k','r','w','e','beta','u','x','vv','qq','A','B','c','d')
    kw = {n:s[n] for n in names}
    kw.update(updates)
    return build(**kw)


def complete_pivots(M, strict_first_three=False):
    block = [list(row) for row in M]
    pivots, blocks = [], []
    for stage in range(5):
        pivot = block[0][0]
        req(pivot != 0, 'Nonzero pivot in this witness')
        req(all(abs(a) <= abs(pivot) for row in block for a in row),
            f'Complete pivoting at stage {stage+1}')
        if strict_first_three and stage < 3:
            req(all(abs(block[i][j]) < abs(pivot)
                    for i in range(len(block)) for j in range(len(block))
                    if (i,j) != (0,0)), f'Strict CP stage {stage+1}')
        blocks.append([row[:] for row in block]); pivots.append(pivot)
        if stage < 4:
            block = [[block[i][j]-block[i][0]*block[0][j]/pivot
                      for j in range(1,len(block))] for i in range(1,len(block))]
    return pivots, blocks


def cofs_left(s):
    be=s['beta']; U,V,T=s['u']; X,Y,Z=s['x']
    return (U-be*X, V-be*Y, be*Z-T, U*Y-X*V, U*Z-T*X, V*Z-T*Y)


def cofs_right(s):
    # p times the first three cofactors, and p times the last three,
    # of the transposed native model. Positive p is never dropped silently.
    p,e=s['p'],s['e']; u,v,w=s['vv']; x,y,z=s['qq']
    return (p*u+e*x, p*v+e*y, -e*z-p*w, u*y-x*v, u*z-x*w, v*z-y*w)


def rank2(a,b):
    return any(a[i]*b[j]-a[j]*b[i] != 0 for i in range(3) for j in range(i+1,3))


def flags(s):
    a,b,c,d = s['A']/s['k'],s['B']/s['k'],s['c'],s['d']
    r,w=s['r']/s['k'],s['w']/s['k']
    u1,u2=s['u'][1:]; v1,v2=s['vv'][1:]
    return dict(
        RL=(r*a*c >= 0 and r*a*d >= 0 and r*r*c*d >= 0 and r*r*u1*u2 <= 0),
        RR=(r*a*c >= 0 and r*b*c >= 0 and r*r*a*b >= 0 and r*r*v1*v2 <= 0),
        SL=(r*b*c >= 0 and w*b*d >= 0 and r*w*c*d >= 0 and r*w*u1*u2 <= 0),
        SR=(r*a*d >= 0 and w*b*d >= 0 and r*w*a*b >= 0 and r*w*v1*v2 <= 0))


def is_macro_r22(s):
    if not (-s['r'] <= s['w'] <= s['r']):
        return False
    f=flags(s)
    ok = not f['RL'] and not f['RR']
    if abs(s['w']) == s['r']:
        ok = ok and not f['SL'] and not f['SR']
    return ok and rank2(s['u'],s['x']) and rank2(s['vv'],s['qq'])


def left_gate(s):
    be=s['beta']; U,V,T=s['u']; X,Y,Z=s['x']; D=s['D']
    return (be*U*X, be*V*Y, be*T*Z, V*T,
            V*(V-be*Y), V*(be*Z-T), be*U*V*(U*Y-X*V),
            -U*V*D[0][1], -U*V*D[0][2], -U*V*D[2][0])


def right_gate(s):
    e,p=s['e'],s['p']; v0,v1,v2=s['vv']; q0,q1,q2=s['qq']; D=s['D']
    return (-e*v0*q0, -e*v1*q1, -e*v2*q2, v1*v2,
            v1*(p*v1+e*q1), v1*(-e*q2-p*v2),
            -e*v0*v1*(v0*q1-q0*v1),
            -v0*v1*D[1][0], -v0*v1*D[2][0], -v0*v1*D[0][2])


def strict_r0(s):
    return (s['beta'] > 0 and all(a > 0 for a in (*s['u'],*s['x']))
            and all(a > 0 for a in cofs_left(s))
            and s['A'] <= 0 and s['B'] <= 0 and s['d'] <= 0)


def weak_r0(s):
    return (s['beta'] >= 0 and all(a >= 0 for a in (*s['u'],*s['x']))
            and all(a >= 0 for a in cofs_left(s))
            and s['A'] <= 0 and s['B'] <= 0 and s['d'] <= 0)


def gauge(M, alpha, theta, eta):
    req(all(a in (-1,1) for a in (alpha,theta,eta)), 'Sign gauge')
    ds=(1,alpha,theta*eta,theta,theta)
    return [[ds[i]*ds[j]*M[i][j] for j in range(5)] for i in range(5)]


def gauges(M):
    for bits in product((-1,1), repeat=3):
        yield bits, gauge(M,*bits)


def sign(a):
    req(a != 0, 'Generic nonzero sign')
    return 1 if a > 0 else -1


def canonical_from_left_gate(M):
    s=extract(M)
    req(all(a > 0 for a in left_gate(s)), 'Left gate not passed')
    U,V,_=s['u']
    out=gauge(M,sign(s['beta']),sign(V),sign(U*V))
    req(strict_r0(extract(out)), 'Explicit R0 gauge')
    return out


def diagonal_contract(M, eta):
    eta=rat(eta); req(0 < eta < Q(1,3), 'Contraction parameter')
    ds=(Q(1),1-eta,1-2*eta,1-3*eta,1-3*eta)
    return [[ds[i]*ds[j]*M[i][j] for j in range(5)] for i in range(5)]


def open_last_corner(M, zeta):
    s=extract(M); zeta=rat(zeta)
    req(zeta > 0 and s['w'] == -s['r'], 'Open the negative full corner')
    out=[row[:] for row in M]; out[4][4] += zeta
    t=extract(out)
    req(-t['r'] < t['w'] < t['r'], 'Strict noncorner')
    complete_pivots(out,strict_first_three=True)
    return out


def is_generic(s):
    critical=(s['e'],s['beta'],*s['u'],*s['x'],*s['vv'],*s['qq'],
              s['A'],s['B'],s['c'],s['d'],*cofs_left(s),*cofs_right(s))
    return all(x != 0 for x in critical)


def residual_cell(s):
    req(is_generic(s), 'Generic signed chart required')
    L,R=left_gate(s),right_gate(s)
    if all(a > 0 for a in L) or all(a > 0 for a in R):
        return None
    return (next(i+1 for i,a in enumerate(L) if a < 0),
            next(i+1 for i,a in enumerate(R) if a < 0))


def regularize_weak_receivers(M, epsilon):
    """Rational regularization of the ordered FOUR rays U,V,beta,T.
    This function does not assume that its epsilon is already small enough
    for CP. The caller must check the rebuilt physical state exactly.
    """
    s=extract(M); eps=rat(epsilon)
    req(weak_r0(s) and 0 < eps < 1, 'Weak R0 and small positive epsilon')
    U,V,T=s['u']; X,Y,Z=s['x']; be=s['beta']
    rays=[(U,X),(V,Y),(be,Q(1)),(T,Z)]
    mass=[a+b for a,b in rays]
    t={i:rays[i][0]/mass[i] for i in range(4) if mass[i] != 0}
    # Virtual endpoint rays; fill each zero run monotonically.
    anchors=[(-1,Q(1))]+sorted(t.items())+[(4,Q(0))]
    for (i,a),(j,b) in zip(anchors,anchors[1:]):
        req(a >= b, 'All six weak minors must be retained')
        for h in range(i+1,j):
            t[h]=(Q(j-h)*a+Q(h-i)*b)/(j-i)
    targets=(Q(4,5),Q(3,5),Q(2,5),Q(1,5))
    newt=[(1-eps)*t[i]+eps*targets[i] for i in range(4)]
    rows={i:((mass[i]+eps)*newt[i],(mass[i]+eps)*(1-newt[i])) for i in (0,1,3)}
    newbeta=newt[2]/(1-newt[2])
    out=rebuild(s,beta=newbeta,u=[rows[i][0] for i in (0,1,3)],
                x=[rows[i][1] for i in (0,1,3)])
    ns=extract(out)
    req(all(a > 0 for a in cofs_left(ns)), 'Strict ordered-ray minors')
    req(ns['F'] == s['F'], 'Receiver regularization preserves the tail height')
    return out


def high_regression_seed(target=Q(206625837,50000000)):
    # Frozen handoff regression, not a newly discovered extremizer.
    t=X=Z=Q(1); be=Q(617533,1000000); V=Q(779151,1000000)
    T=Q(18129,40000); Y=Q(1414807,1453225); f=rat(target)
    p=(1+T)/Z; r=f/2
    de=1-be*X; ga=V-be*Y; nu=be*Z-T; mu=V*Z-T*Y; Qp=t*de-ga
    at=1-Y+ga*(1+X)/de; ct=1+Z+nu*(1+X)/de
    E=(nu*(r-at)+Qp*(r-ct))/(de*(r-at))
    k=(p*mu+Y*(V+T))/(V*(t*Z+E*Y)); b=de*(r-at)/Qp
    A1=1+Y+t*(1-X); A2=(t*(1+Z)+E*(1+Y))/(t+E)
    B2=(t*nu-E*ga)/(t+E)
    h=max(Q(0),(r-A1)/Qp,(r-A2)/B2)
    a=(r-1-Y+ga*h)/t; v=(b-1-X)/de
    q=1-be*v; g=(p-1)/V; j=(t*k-p)/Y
    M=build(p=p,k=k,r=r,w=-r,e=Q(1),beta=be,u=[Q(1),V,T],x=[X,Y,Z],
            vv=[-g,h,v],qq=[-j,-1-be*h,q],A=-a,B=-b,c=t,d=-E)
    piv,_=complete_pivots(M)
    req(piv == [1,p,k,r,-f], 'Frozen high witness pivots')
    return M


def small_example(beta=Q(1,4), u=None, x=None, residual=False):
    if u is None: u=[Q(1,4),Q(1,4),Q(1,8)]
    if x is None: x=[Q(1,8),Q(1,4),Q(1,2)]
    return build(p=Q(1,2),k=Q(1,4),r=Q(1,8),
                 w=Q(-31,250) if residual else Q(-1,8),
                 e=Q(1,4),beta=beta,u=u,x=x,
                 vv=[Q(-1,8),Q(1,8),Q(1,8)],
                 qq=[Q(-1,8),Q(-1,8),Q(1,10) if residual else Q(1,8)],
                 A=Q(-1,8),B=Q(-1,8),c=Q(1,2),d=Q(-1,4))
