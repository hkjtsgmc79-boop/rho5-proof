"""Exact high-value elimination for a fixed R0 left frame.

No optimization package, floating-point acceptance, or numerical root isolation.
The theorem is conditional on the strict-positive-cofactor sharp domain.
It computes the exact maximum whenever that maximum is >= 33/8;
otherwise it certifies only that no completion reaches 33/8.
"""
from __future__ import annotations
from fractions import Fraction as Q
from typing import Any
from model import State, derived, check_state, require, PARAMS, rational

THRESHOLD=Q(33,8)

def frame_data(theta: dict[str,Q]) -> dict[str,Q]:
    t,E,be,U,V,T,X,Y,Z=[rational(theta[n]) for n in PARAMS]
    require(U==1 and 0<V<1,'sharp frame U=1, V<1')
    require(-1<=t<=1 and 0<=E<=1,'t and E boxes')
    require(all(0<x<=1 for x in [be,V,T,X,Y,Z]),'positive frame boxes')
    de=1-be*X; ga=V-be*Y; nu=be*Z-T
    ta=Y-X*V; De=Z-T*X; mu=V*Z-T*Y
    require(all(x>0 for x in [de,ga,nu,ta,De,mu]),'strict positive cofactors')
    return dict(t=t,E=E,beta=be,V=V,T=T,X=X,Y=Y,Z=Z,delta=de,gamma=ga,nu=nu,tau=ta,Delta=De,mu=mu,
                Qp=t*de-ga,Omega=t*De+E*ta-mu,zeta=t*nu-E*ga)

def first_capacity(d: dict[str,Q],p: Q) -> dict[str,Any]:
    t,E,be,V,T,X,Y,Z,de,ga,nu,ta,De,mu=[d[n] for n in ['t','E','beta','V','T','X','Y','Z','delta','gamma','nu','tau','Delta','mu']]
    # Lower lines A_i*k-B_i; upper lines C_j-D_j*k.
    lower=[(1/X,p/X),(t/Y,p/Y),(t/Y,(1+V)/Y)]
    upper=[((1+be)/de,be/de),((1+T)/De,(E+T)/De),
           ((V+be)/ga,be*t/ga),((V+T)/mu,(V*E+T*t)/mu)]
    caps=[(f'K{i+1}{j+1}',(B+C)/(A+D)) for i,(A,B) in enumerate(lower) for j,(C,D) in enumerate(upper)]
    k=min(v for _,v in caps)
    jl=max(A*k-B for A,B in lower);ju=min(C-D*k for C,D in upper)
    g=max(k-1-X*jl,(t*k-1-Y*jl)/V)
    return dict(k=k,j=jl,g=g,j_upper=ju,caps=caps,lower=lower,upper=upper)

def middle_capacity(d: dict[str,Q],p: Q,k: Q) -> dict[str,Any]:
    t,E,be,X,Y,Z,ga,nu,qp,ze=[d[n] for n in ['t','E','beta','X','Y','Z','gamma','nu','Qp','zeta']]
    H=(p-1)/be
    inc=[(1+Y+t*(1-X),qp),((t*(1+Z)+E*(1+Y))/(t+E),ze/(t+E))]
    dec=[(1+Y+t*(p-X),ga+t*be*X),((t*k+E*(1+Y))/(t+E),E*ga/(t+E))]
    caps=[(f'D{j+1}@0',C) for j,(C,D) in enumerate(dec)]
    caps += [(f'I{i+1}@H',A+B*H) for i,(A,B) in enumerate(inc)]
    caps += [(f'I{i+1}D{j+1}',(B*C+D*A)/(B+D)) for i,(A,B) in enumerate(inc) for j,(C,D) in enumerate(dec)]
    R=min(v for _,v in caps)
    return dict(R=R,H=H,inc=inc,dec=dec,caps=caps)

def middle_at_r(d: dict[str,Q],middle: dict[str,Any],r: Q) -> tuple[Q,Q]:
    h=max([Q(0)]+[(r-A)/B for A,B in middle['inc']])
    a=(r-1-d['Y']+d['gamma']*h)/d['t']
    return a,h

def make_state(theta: dict[str,Q],p:Q,first:dict[str,Any],middle:dict[str,Any],b:Q,r:Q,w:Q,v:Q,q:Q) -> State:
    d=frame_data(theta);a,h=middle_at_r(d,middle,r)
    z={'p':p,'e':Q(1),'k':first['k'],'a':a,'b':b,'r':r,'w':w,
       'v0':-first['g'],'q0':-first['j'],'v1':h,'q1':-1-d['beta']*h,'v2':v,'q2':q}
    return State({n:rational(theta[n]) for n in PARAMS},z)

def tail_candidates(d:dict[str,Q],p:Q,k:Q,R:Q) -> list[dict[str,Any]]:
    t,E,be,V,T,X,Y,Z,de,ga,nu,ta,De,mu,qp,Om=[d[n] for n in ['t','E','beta','V','T','X','Y','Z','delta','gamma','nu','tau','Delta','mu','Qp','Omega']]
    s=p-1;lo=1+X;hi=min(k,1+X+de*s)
    ar=1-Y+ga*(1+X)/de;br=qp/de
    ac=1+Z+nu*(1+X)/de;bc=E-nu/de
    result=[]
    if lo<=hi:
        bs=[('A:left',lo),('A:right',hi),('A:Rtail=R',(R-ar)/br)]
        if br!=bc:bs.append(('A:Rtail=Ctail',(ac-ar)/(br-bc)))
        if bc!=0:bs.append(('A:Ctail=R',(R-ac)/bc))
        seen=set()
        for name,b in bs:
            if not lo<=b<=hi or b in seen:continue
            seen.add(b);r=min(R,ar+br*b);C=ac+bc*b;w=-min(r,C)
            v=(b-1-X)/de;q=(1+be-be*b)/de
            result.append(dict(name=name,b=b,r=r,w=w,v=v,q=q,F=r-w,eligible=r-w>=THRESHOLD))
    rB=min(R,(mu+De+ta+Om*k)/(De+ta))
    vB=(X*rB-(t*X-Y)*k-X-Y)/ta
    qB=(1+V+(t-V)*k-rB)/ta
    PB=be*vB+qB
    eligible=2*rB>=THRESHOLD and 0<=vB<=s and qB>=0 and 0<=PB<=1
    result.append(dict(name='B:wall_corner',b=k,r=rB,w=-rB,v=vB,q=qB,F=2*rB,eligible=eligible))
    return result

def solve_frame(theta:dict[str,Q],verify:bool=True)->dict[str,Any]:
    d=frame_data(theta)
    necessary=[('t>V',d['t']>d['V']),('Delta>tau',d['Delta']>d['tau']),
               ('X>1/(1+beta)',d['X']>1/(1+d['beta'])),('zeta>0',d['zeta']>0)]
    for name,ok in necessary:
        if not ok:return dict(status='BELOW_THRESHOLD',reason=name+' fails (necessary for F>4)')
    p=(1+d['T'])/d['Z']
    if not p<1+d['beta']:return dict(status='BELOW_THRESHOLD',reason='head capacity <=2 in r')
    first=first_capacity(d,p)
    if first['k']<=2:return dict(status='BELOW_THRESHOLD',reason='K<=2',p=p,first=first)
    middle=middle_capacity(d,p,first['k'])
    if 2*middle['R']<THRESHOLD:return dict(status='BELOW_THRESHOLD',reason='2*R<threshold',p=p,first=first,middle=middle)
    cand=tail_candidates(d,p,first['k'],middle['R'])
    accepted=[]
    for c in cand:
        if not c['eligible']:continue
        st=make_state(theta,p,first,middle,c['b'],c['r'],c['w'],c['v'],c['q'])
        if verify:check_state(st,c['name'])
        c['state']=st;accepted.append(c)
    if not accepted:return dict(status='BELOW_THRESHOLD',reason='no eligible high tail candidate',p=p,first=first,middle=middle,candidates=cand)
    best=max(accepted,key=lambda c:c['F'])
    return dict(status='HIGH_MAXIMUM',F=best['F'],state=best['state'],winner=best['name'],p=p,first=first,middle=middle,candidates=cand)
