"""V42 exact whole-box B01/B02 port. No source is asserted to exist.
Input: an enclosure of the SAME complete B24 canonical maximum image.
This file alone does not certify a B17->B24 enclosure; use bound_protocol.py.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
import json

B_NAMES=('k','r','s','t','A','B','c','d','p','e','beta','u0','u1','u2','x0','x1','x2','v0','v1','v2','q0','q1','q2','F')
X_NAMES=('k','r','w','A','B','c','d','p','e','beta','u0','u1','u2','x0','x1','x2','v0','v1','v2','q0','q1','q2')
RHO=Q(1,1250); COST=Q(200,3); GAMMA=Q(4132517,10**6)
ONE_SLACK_COSTS=(Q(13,4),Q(36),Q(15,8),Q(55))
class Empty(ValueError):pass

def rational(x):
    if type(x) not in (str,int,Q):raise ValueError('Exact integers/fractions only')
    return Q(x)
@dataclass(frozen=True)
class I:
    lo:Q
    hi:Q
    def __post_init__(self):
        object.__setattr__(self,'lo',rational(self.lo));object.__setattr__(self,'hi',rational(self.hi))
        if self.lo>self.hi:raise Empty('reversed interval')
    @staticmethod
    def cast(x):return x if isinstance(x,I) else I(x,x)
    def __add__(self,o):
        o=I.cast(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-I.cast(o)
    def __rsub__(self,o):return I.cast(o)+-self
    def __mul__(self,o):
        o=I.cast(o);v=[a*b for a,b in product((self.lo,self.hi),(o.lo,o.hi))];return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=I.cast(o)
        if o.lo<=0<=o.hi:raise ValueError('uncertified nonzero denominator')
        return self*I(1/o.hi,1/o.lo)
    def sq(self):return I(0 if self.lo<=0<=self.hi else min(self.lo**2,self.hi**2),max(self.lo**2,self.hi**2))
    def meet(self,o):
        o=I.cast(o);return I(max(self.lo,o.lo),min(self.hi,o.hi))
    def abs_upper(self):return max(abs(self.lo),abs(self.hi))
    def data(self):return [str(self.lo),str(self.hi)]

def load_box(data):
    if not isinstance(data,list) or len(data)!=24:raise ValueError('B24 coordinate count')
    out={n:I(*p) for n,p in zip(B_NAMES,data)}
    if min(out[n].lo for n in ('k','p','r'))<=0:raise ValueError('Positive pivots need positive enclosure lower bounds')
    return out

def transpose(z):
    """Actual J0 M^T J0, J0=diag(1,-1,1,1,1)."""
    o=dict(z);p=z['p'];k=z['k']
    o['e'],o['beta']=z['beta'],z['e'];o['s'],o['t']=z['t'],z['s']
    o['A'],o['B'],o['c'],o['d']=z['c']*k,z['d']*k,z['A']/k,z['B']/k
    for i in range(3):
        o[f'u{i}'],o[f'v{i}']=z[f'v{i}'],z[f'u{i}']
        o[f'x{i}'],o[f'q{i}']=-z[f'q{i}']/p,-p*z[f'x{i}']
    return o

def diagonal(z,signs):
    """Actual diag(1,a,b,c,c) congruence. H and F unchanged."""
    a,b,c=signs
    if any(type(s)is not int or s not in(-1,1) for s in signs):raise ValueError('sign')
    o=dict(z);o['e']=a*z['e'];o['beta']=a*z['beta']
    for n in ('A','B','c','d'):o[n]=b*c*z[n]
    for i,h in enumerate((b,c,c)):
        for n in ('u','v'):o[f'{n}{i}']=h*z[f'{n}{i}']
        for n in ('x','q'):o[f'{n}{i}']=a*h*z[f'{n}{i}']
    return o

def opposite_pivot(z):
    """Actual Q M Q, Q=diag(I3, [[0,-1],[1,0]])."""
    o=dict(z);o['s'],o['t']=z['t'],z['s']
    o['A'],o['B'],o['c'],o['d']=z['B'],-z['A'],-z['d'],z['c']
    for n in ('u','x'):o[n+'1'],o[n+'2']=-z[n+'2'],z[n+'1']
    for n in ('v','q'):o[n+'1'],o[n+'2']=z[n+'2'],-z[n+'1']
    return o

def ordered_branches(z):
    """Two closed sorting branches cover equality as well. No strict cut."""
    for sw in (False,True):
        q=dict(z)
        try:
            # Branch is s>=t (or t>=s before QMQ), with 0<=s,t<=r.
            if sw:q=opposite_pivot(q)
            for _ in range(3):
                q['r']=q['r'].meet(I(max(q['s'].lo,q['t'].lo,0),q['r'].hi))
                q['s']=q['s'].meet(I(max(0,q['t'].lo),q['r'].hi))
                q['t']=q['t'].meet(I(0,min(q['s'].hi,q['r'].hi)))
            yield sw,q
        except Empty:continue

def target(z):
    """Guaranteed enclosure on 0<=t<=s<=r; common source coefficients."""
    r,s,t=z['r'],z['s'],z['t']
    g=(r-s).meet(I(0,r.hi));h=(s-t).meet(I(0,r.hi))
    Z=(2*r+t-s).meet(I(r.lo,2*r.hi));rs=r+s
    mu=(g/Z).meet(I(0,Q(1,2)))
    lam=1-mu
    R=((r.sq()+s*t)/Z).meet(I(r.lo/2,r.hi)).meet(r-mu*(r+t))
    nu=(mu*(r+t)/rs).meet(I(0,mu.hi)).meet((r-R)/rs)
    xi=1-nu
    delta=(2*R*h/rs).meet(I(0,R.hi))
    T=(R*(r+2*t-s)/rs).meet(I(0,R.hi)).meet(R-delta)
    delta=delta.meet(R-T)
    loss=(g*delta/(2*r)).meet(I(0,GAMMA if 'F' not in z else max(Q(0),z['F'].hi)))
    # The same positive formula avoids catastrophic F-F_X cancellation.
    loss=loss.meet(g*R*h/(r*rs))
    out={n:z[n] for n in X_NAMES if n in z}
    out.update(r=R,w=-T,A=z['B'],B=z['A'],c=lam*z['c']-mu*z['d'],d=-nu*z['c']-xi*z['d'])
    for n in ('u','x'):
        out[n+'1']=lam*z[n+'1']-mu*z[n+'2']
        out[n+'2']=-nu*z[n+'1']-xi*z[n+'2']
    for n in ('v','q'):out[n+'1'],out[n+'2']=z[n+'2'],z[n+'1']
    return out,dict(mu=mu,nu=nu,g=g,h=h,Z=Z,R=R,T=T,delta=delta,loss=loss)

def port_for_orientation(z,centers,method='one_slack'):
    if method not in ('legacy','one_slack'):raise ValueError('unknown proved method')
    branches=[]
    for swapped,src in ordered_branches(z):
        try:X,t=target(src)
        except Empty:
            # Intersection of universally valid enclosures is empty.
            branches.append(dict(swapped=swapped,status='EMPTY_BRANCH'));continue
        losses=t['loss'];candidates=[]
        for j,cen in enumerate(centers):
            ds=[(X[n]-rational(c)).abs_upper() for n,c in zip(X_NAMES,cen)]
            D=max(ds);LU=losses.hi;cost=COST if method=='legacy' else ONE_SLACK_COSTS[j];score=D+cost*LU
            # A lower bound on distance allows rigorous exclusion of the LOCAL PORT,
            # not of complete physical sources.
            dl=[]
            for n,c in zip(X_NAMES,cen):
                c=rational(c);v=X[n];dl.append(max(Q(0),v.lo-c,c-v.hi))
            candidates.append(dict(center=j,cost=str(cost),distance_upper=str(D),loss_upper=str(LU),score_upper=str(score),
                distance_lower=str(max(dl)),decisive_coordinate=X_NAMES[ds.index(D)],
                local_domain_disjoint=max(dl)>RHO,accepted=score<=RHO))
        ok=losses.hi==0 or any(c['accepted'] for c in candidates)
        best=min(candidates,key=lambda c:Q(c['score_upper']))
        branches.append(dict(swapped=swapped,status='SAFE_ALPHA' if ok else 'OPEN',zero_loss=losses.hi==0,
            source={n:src[n].data() for n in B_NAMES},target={n:X[n].data() for n in X_NAMES},
            common_quantities={n:v.data() for n,v in t.items()},centers=candidates,best_center=best['center']))
    status='SAFE_ALPHA' if branches and all(b['status'] in ('SAFE_ALPHA','EMPTY_BRANCH') for b in branches) else 'OPEN'
    return dict(status=status,branches=branches)

def check_box(box,centers,symmetries=False,method='one_slack'):
    z=load_box(box)
    if len(centers)!=4 or any(len(c)!=22 for c in centers):raise ValueError('Four frozen X22 centers required')
    choices=[(False,False,(1,1,1))]
    if symmetries:
        choices=[(tr,pv,sig) for tr,pv,sig in product((False,True),(False,True),list(product((-1,1),repeat=3)))]
    tries=[]
    for tr,pv,sig in choices:
        q=transpose(z) if tr else z
        if pv:q=opposite_pivot(q)
        q=diagonal(q,sig)
        val=port_for_orientation(q,centers,method);val['orientation']=[tr,pv,list(sig)]
        tries.append(val)
        if val['status']=='SAFE_ALPHA':return dict(status='SAFE_ALPHA',selected=val,tried=len(tries))
    # All alternatives are diagnostic only if no complete orientation succeeds.
    return dict(status='OPEN',attempts=tries,tried=len(tries))
