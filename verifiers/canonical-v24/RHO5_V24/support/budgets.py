"""V16 exact high-value envelope.  No floating-point or optimization dependency.

The new slope-exclusion theorem rejects nu - E*delta <= 0.
For the other frames, six explicit rational budgets replace tail candidates.
The first and middle capacity computations are the unchanged V15 dependency.
"""
from __future__ import annotations
from fractions import Fraction as Q
from typing import Any
from model import State, require, rational, PARAMS, check_state
import v15_capacities as v15

H0=Q(33,8)

def tail_data(d:dict[str,Q], K:Q, R:Q)->dict[str,Q]:
    de,ga,nu,ta,De,mu,qp,Om=[d[n] for n in ['delta','gamma','nu','tau','Delta','mu','Qp','Omega']]
    L=nu-d['E']*de
    require(L>0,'V16 tail data requires the positive slope gap')
    sig=qp-L
    A=mu+De+ta
    B=De+nu+de
    C=A+Om*K
    D=L*A+Om*B
    N=L*ta+Om*de
    u=De-ta
    b0=1+d['X']
    C0=1+d['Z']+d['E']*b0
    require(all(x>0 for x in [de,ta,De,mu,qp,Om,L,N,u]),'positive denominators')
    require(C0==(B-L*b0)/de,'tail constant identity')
    require(De*sig==N-L*De,'slope identity')
    return dict(L=L,sigma=sig,A=A,B=B,C=C,D=D,N=N,u=u,b0=b0,C0=C0,K=K,R=R)

def six_budgets(d:dict[str,Q],K:Q,R:Q)->tuple[list[tuple[str,Q]],dict[str,Q]]:
    z=tail_data(d,K,R)
    L,sg,A,B,C,D,N,u,b0,C0=[z[n] for n in ['L','sigma','A','B','C','D','N','u','b0','C0']]
    de,ta,De,Om=[d[n] for n in ['delta','tau','Delta','Omega']]
    caps=[('middle:2R',2*R),('tail:wall-K',2*C/(De+ta)),
          ('lower-b:R+C0',R+C0),('lower-b:K+C0',(C+u*C0)/De)]
    if sg>=0:
        caps += [('positive-sigma:middle-contact',(D+De*sg*R)/N),
                 ('positive-sigma:K-contact',(D*u+C*De*sg)/(Om*de*De))]
    else:
        caps += [('negative-sigma:wall-contact',2*D/(L*(De+ta)+Om*de)),
                 ('negative-sigma:lower-b-contact',(D-De*sg*C0)/(L*De))]
    return caps,z

def reconstruct(d:dict[str,Q],theta:dict[str,Q],p:Q,first:dict[str,Any],middle:dict[str,Any],
                F:Q,z:dict[str,Q])->tuple[State,dict[str,Any]]:
    K,R=first['k'],middle['R']
    L,sg,C,D,N,u,C0,b0,B=[z[n] for n in ['L','sigma','C','D','N','u','C0','b0','B']]
    de,ta,De,Om,qp=[d[n] for n in ['delta','tau','Delta','Omega','Qp']]
    lo=max(F/2,F-C0)
    hi=min(R,(C-ta*F)/u)
    if sg>0:lo=max(lo,(N*F-D)/(De*sg))
    elif sg<0:hi=min(hi,(D-N*F)/(-De*sg))
    else:require(N*F<=D,'zero-sigma budget')
    require(lo<=hi,'nonempty exact (r,-w) interval')
    r=lo;y=F-r
    require(2<r<=R and 0<y<=r,'high-value height coordinates')
    rt0=1-d['Y']+d['gamma']*b0/de
    slope=qp/de
    rtK=rt0+slope*K
    if r==y:
        if r<=rtK:
            b=max(b0,(r-rt0)/slope)
            v=(b-b0)/de;q=1-d['beta']*v
            kind='A:wall'
        else:
            b=K
            v=(d['X']*r-(d['t']*d['X']-d['Y'])*K-d['X']-d['Y'])/ta
            q=(1+d['V']+(d['t']-d['V'])*K-r)/ta
            kind='B:wall-corner'
    elif y==C0:
        b=b0;v=Q(0);q=Q(1);kind='A:lower-b'
    else:
        require(L*De*r+N*y==D,'nonwall optimum must hit the second oblique line')
        b=(B-de*y)/L
        v=(b-b0)/de;q=1-d['beta']*v
        require(rt0+slope*b==r,'nonwall contact R_T(b)=r')
        kind='A:nonwall-contact'
    require(b0<=b<=K,'reconstructed b range')
    st=v15.make_state(theta,p,first,middle,b,r,-y,v,q)
    require(st.F==F,'objective preserved by reconstruction')
    check_state(st,kind)
    return st,dict(kind=kind,r_low=lo,r_high=hi,r=r,y=y,b=b)

def solve_frame(theta:dict[str,Q],verify:bool=True)->dict[str,Any]:
    d=v15.frame_data(theta)
    necessities=[('t>V',d['t']>d['V']),('Delta>tau',d['Delta']>d['tau']),
                 ('X>1/(1+beta)',d['X']>1/(1+d['beta'])),('zeta>0',d['zeta']>0)]
    for name,ok in necessities:
        if not ok:return dict(status='BELOW_THRESHOLD',reason=name+' fails (V15)')
    gap=d['nu']-d['E']*d['delta']
    if gap<=0:return dict(status='BELOW_THRESHOLD',reason='V16 slope-exclusion theorem: nu-E*delta<=0')
    p=(1+d['T'])/d['Z']
    if not p<1+d['beta']:return dict(status='BELOW_THRESHOLD',reason='V15 head capacity')
    first=v15.first_capacity(d,p)
    if first['k']<=2:return dict(status='BELOW_THRESHOLD',reason='V15 K<=2')
    middle=v15.middle_capacity(d,p,first['k'])
    if 2*middle['R']<H0:return dict(status='BELOW_THRESHOLD',reason='V15 2R<threshold')
    caps,z=six_budgets(d,first['k'],middle['R'])
    F=min(v for _,v in caps)
    out=dict(status='BELOW_THRESHOLD' if F<H0 else 'HIGH_MAXIMUM',p=p,first=first,middle=middle,
             caps=caps,tail=z,high_layer_bound=F,active=[n for n,v in caps if v==F])
    if F>=H0:
        st,rec=reconstruct(d,theta,p,first,middle,F,z)
        if verify:check_state(st,'V16 reconstructed maximum')
        out.update(F=F,state=st,reconstruction=rec)
    return out
