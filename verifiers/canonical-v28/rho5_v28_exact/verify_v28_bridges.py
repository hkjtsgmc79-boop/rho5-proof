"""Exact transport, domain margins, and 6D-to-9D localization bridges.
These are separate obligations from the Jacobian and root certificates.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
BASE=Path(__file__).resolve().parent
class I:
    def __init__(self,a,b=None):
        self.lo=Q(a);self.hi=Q(a if b is None else b)
        if self.lo>self.hi:raise ValueError('bad interval')
    def __add__(self,o):o=iv(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-iv(o)
    def __rsub__(self,o):return iv(o)+-self
    def __mul__(self,o):
        o=iv(o);z=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi];return I(min(z),max(z))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=iv(o)
        if o.lo<=0<=o.hi:raise ZeroDivisionError('denominator includes zero')
        x,y=Q(1)/o.lo,Q(1)/o.hi;return self*I(min(x,y),max(x,y))
    def __rtruediv__(self,o):return iv(o)/self

def iv(o):return o if isinstance(o,I) else I(o)
BOX={'beta':('0.617','0.6181'),'V':('0.7788','0.7795'),'s':('0.4525','0.4540'),
     'Y':('0.97352','0.97361'),'Z':('0.99998','1'),'v':('0.1944','0.19501'),
     'h':('0.4513','0.4566'),'b':('2.0741','2.0748'),'R':('1.0662585','1.06626')}
cert=json.loads((BASE/'RHO5_V26_REBUILT/jacobian_recovered_certificate.json').read_text())
name={'be':'beta','ss':'s'}
for k,ab in cert['box'].items():
    assert tuple(map(Q,ab))==tuple(map(Q,BOX[name.get(k,k)]))
    assert Q(cert['center'][k])==sum(map(Q,ab))/2
assert len(cert['box'])==9 and all(Q(r)>0 for r in cert['rho'])
x={k:I(*ab) for k,ab in BOX.items()}
def calc(x):
    be,V,s,Y,Z,v,h,b,R=(x[k] for k in ('beta','V','s','Y','Z','v','h','b','R'))
    p=1+s;r=R+1;eps=R-1;T=p*Z-1;q=1-be*v;ga=V-be*Y;nu=be*Z-T;mu=V*Z-T*Y
    A=R+Y+ga*v;C=R-Z+nu*v;W=R*(Y+Z)+mu*v;N=V*(Y+Z)+s*mu
    Dh=mu+R*(nu-ga);d1=1-V-be*eps;ah=eps*(1+q)-(1-V)*v
    aa=R*(1+q)+V*v;dS=V+be*(eps-v);sh=p*q+1+v-aa
    hA=ah/d1;hS=sh/dS;B0=2+(1-be)*v
    lam=N/(V*W);g=s/V;j=(lam*A-p)/Y;X=(b-1-v)/q;k=lam*b;E=C/b
    S00=k-X*j
    return locals()
D=calc(x);checks={}
def lower(label,z,bound=0):
    z=iv(z);bound=Q(bound);assert z.lo>bound,(label,float(z.lo),str(bound));checks[label]={'lo':str(z.lo),'hi':str(z.hi),'strict_lower':str(bound)}
def upper(label,z,bound):
    z=iv(z);bound=Q(bound);assert z.hi<bound,(label,float(z.hi),str(bound));checks[label]={'lo':str(z.lo),'hi':str(z.hi),'strict_upper':str(bound)}
# Bound the independent fixed f_minus representative before target transport.
xlow=dict(x);xlow['v']=I('0.1944','0.1950');xlow['R']=I(Q(2132517,2000000));d=calc(xlow)
lower('Q_old_transport',d['A']/d['B0']*(1-d['be'])-d['ga'],Q(1,5))
step=(Q(53313,50000)-Q(2132517,2000000))*5
assert step==Q(3,400000) and step<Q(1,100000)
# Enclosures of b,h, valid for actual states by their shared physical inequalities.
lower('A_to_b_lower',D['A'],Q(20741,10000));upper('B0_to_b_upper',D['B0'],Q(5187,2500))
lower('hA_to_h_lower',D['hA'],Q(4513,10000));upper('hS_to_h_upper',D['hS'],Q(2283,5000))
for nm in ['q','ga','nu','mu','A','C','W','N','Dh','d1','dS','j','g','T']:
    lower('positive_'+nm,D[nm])
upper('T_upper',D['T'],1);upper('g_upper',D['g'],1);upper('E_upper',D['E'],1)
lower('v_positive',D['v']);lower('s_minus_v',D['s']-D['v']);lower('s_positive',D['s'])
lower('beta_minus_s',D['be']-D['s']);lower('H_minus_h',D['s']/D['be']-D['h'])
Pcal=D['eps']*D['V']*((D['Y']+D['Z'])-D['v']*(D['nu']-D['ga']))-(D['s']-D['V']*D['v'])*D['Dh']
lower('one_minus_j_minus_beta_g',Pcal/(D['V']*D['W']),Q(1,1000))
lower('p_minus_S00',D['p']-D['S00'],Q(1,200))
lower('head_L1_margin',1-D['p']*D['Y']+D['V']);lower('five_minus_F_beta',5-2*(D['R']+1)-D['be'])
lower('X_positive',D['X']);lower('b_minus_1_v',D['b']-1-D['v'])
# These three cofactors use the actual nonnegative G2, i.e. X<=1.
lower('delta_given_X_le_1',1-D['be']);lower('tau_given_X_le_1',D['Y']-D['V']);lower('Delta_given_X_le_1',D['Z']-D['T'])
# Uniform strict original box margins (Z<=1 is one of the eight explicit guards).
for nm in ['beta','V','Y']:lower(nm+'_positive',D.get(nm,x[nm]));upper(nm+'_below_one',D.get(nm,x[nm]),1)
res={'status':'V28_EXACT_TRANSPORT_AND_COMPACTNESS_BRIDGES_PASS','checks':checks,'transport_delta_v_strict_upper':'1/100000','transport_computable_bound':str(step)}
(BASE/'bridge_verification.json').write_text(json.dumps(res,indent=2))
print(res['status'],len(checks))
for k in ['Q_old_transport','A_to_b_lower','B0_to_b_upper','hA_to_h_lower','hS_to_h_upper','one_minus_j_minus_beta_g','p_minus_S00']:
    z=checks[k];print(k,float(Q(z['lo'])),float(Q(z['hi'])))
