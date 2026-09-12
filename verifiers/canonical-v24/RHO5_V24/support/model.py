"""Independent Fraction implementation of the complete R0 physical model.

All acceptance arithmetic is rational.  The 91 scalar rows are generated directly
from their semantic formulas, independently of the inherited SymPy LP builder.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Any

PARAMS = ['t','E','beta','U','V','T','X','Y','Z']
VARS = ['k','a','b','r','w','p','e','v0','q0','v1','q1','v2','q2']

def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)

def rational(x: str | int | Q) -> Q:
    if isinstance(x, float):
        raise TypeError('Floating-point input is not an exact certificate')
    return Q(x)

@dataclass
class State:
    theta: dict[str,Q]
    primal: dict[str,Q]

    @classmethod
    def from_json(cls, data: dict[str,Any]) -> State:
        return cls({n:rational(data['theta'][n]) for n in PARAMS},
                   {n:rational(data['primal'][n]) for n in VARS})

    def to_json(self) -> dict[str,Any]:
        return {'theta':{n:str(self.theta[n]) for n in PARAMS},
                'primal':{n:str(self.primal[n]) for n in VARS}}

    def copy(self) -> State:
        return State(dict(self.theta),dict(self.primal))

    @property
    def F(self) -> Q:
        return self.primal['r']-self.primal['w']


def derived(st: State) -> dict[str,Any]:
    th,z=st.theta,st.primal
    t,E,be,U,V,T,X,Y,Z=[th[n] for n in PARAMS]
    k,a,b,r,w,p,e=[z[n] for n in VARS[:7]]
    u=[U,V,T];x=[X,Y,Z]
    v=[z[f'v{i}'] for i in range(3)];q=[z[f'q{i}'] for i in range(3)]
    D=[[k,-a,-b],[t*k,r-t*a,r-t*b],[-E*k,r+E*a,w+E*b]]
    S=[[D[i][j]+x[i]*q[j] for j in range(3)] for i in range(3)]
    O=[[S[i][j]+u[i]*v[j] for j in range(3)] for i in range(3)]
    P=[be*v[j]+q[j] for j in range(3)]
    L=[p*x[i]-e*u[i] for i in range(3)]
    M=[[Q(1),-e,*v],[be,p-e*be,*P]]+[[u[i],L[i],*O[i]] for i in range(3)]
    cof={'delta':U-be*X,'nu':be*Z-T,'gamma':V-be*Y,
         'tau':U*Y-X*V,'Delta':U*Z-T*X,'mu':V*Z-T*Y}
    return dict(D=D,S=S,O=O,P=P,L=L,M=M,u=u,x=x,v=v,q=q,cof=cof)


def scalar_slacks(st: State) -> list[tuple[str,Q]]:
    d=derived(st);z=st.primal;th=st.theta;rows=[]
    p,k,r,w=z['p'],z['k'],z['r'],z['w']
    def band(value: Q, bound: Q, label: str) -> None:
        rows.extend([(label+'+',bound-value),(label+'-',bound+value)])
    band(z['e'],Q(1),'e');band(p-z['e']*th['beta'],Q(1),'H')
    for i in range(3):band(d['L'][i],Q(1),f'L{i}')
    for j in range(3):
        band(d['v'][j],Q(1),f'v{j}');band(d['q'][j],p,f'q{j}')
        band(d['P'][j],Q(1),f'P{j}')
        for i in range(3):
            band(d['S'][i][j],p,f'S{i}{j}');band(d['O'][i][j],Q(1),f'O{i}{j}')
    for i in range(3):
        for j in range(3):band(d['D'][i][j],k,f'D{i}{j}')
    for n in ['p','k','r']:rows.append((n+'>=0',z[n]))
    band(w,r,'w')
    for n in ['a','b']:rows.extend([(n+'>=0',z[n]),(n+'<=k',k-z[n])])
    require(len(rows)==91,'91 semantic rows')
    return rows


def cp_pivots(M: list[list[Q]]) -> list[Q]:
    block=[row[:] for row in M];ans=[]
    for stage in range(5):
        pivot=block[0][0]
        require(pivot!=0,f'Zero pivot at stage {stage+1}')
        require(all(abs(x)<=abs(pivot) for row in block for x in row),
                f'Complete pivot violated at stage {stage+1}')
        ans.append(pivot)
        if stage<4:
            block=[[block[i][j]-block[i][0]*block[0][j]/pivot
                    for j in range(1,len(block))] for i in range(1,len(block))]
    return ans


def rank_two(a: list[Q], b: list[Q]) -> bool:
    return any(a[i]*b[j]-a[j]*b[i]!=0 for i in range(3) for j in range(i+1,3))


def check_state(st: State, label: str = '', require_middle: bool = True) -> dict[str,Any]:
    th,z=st.theta,st.primal;d=derived(st)
    require(-1<=th['t']<=1 and 0<=th['E']<=1,label+': t/E bounds')
    require(all(0<th[n]<=1 for n in ['beta','U','V','T','X','Y','Z']),label+': positive boxes')
    require(all(x>0 for x in d['cof'].values()),label+': strict cofactors')
    if require_middle:
        require(z['e']==1 and th['U']==1 and d['P'][1]==-1,label+': sharp middle face')
    for name,slack in scalar_slacks(st):
        require(slack>=0,f'{label}: {name} failed: {slack}')
    require(cp_pivots(d['M'])==[Q(1),z['p'],z['k'],z['r'],-st.F],label+': pivot dictionary')
    require(rank_two(d['u'],d['x']) and rank_two(d['v'],d['q']),label+': packet ranks')
    return d
