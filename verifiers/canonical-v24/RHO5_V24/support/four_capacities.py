"""V19: four first-column capacities, exact at the certified high layer.

IMPORTANT: the provisional first column need not be physical by itself.  The
common tail budget is used in the theorem to recover its omitted O00 upper band.
Only a HIGH_MAXIMUM output is a complete physical maximum.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import sys,json
sys.path.insert(0,str(Path(__file__).resolve().parent/'support'))
import v15_capacities as v15
import budgets
from model import rational,check_state,derived,require,PARAMS
H0=Q(33,8)


def first_capacity_four(d,p):
    t,E,be,V,T,X,Y,Z,ga,mu=[d[n] for n in ['t','E','beta','V','T','X','Y','Z','gamma','mu']]
    caps=[('K13',(p*ga+X*(V+be))/(ga+be*t*X)),
          ('K14',(p*mu+X*(V+T))/(mu+X*(V*E+T*t))),
          ('K23',(p*ga+Y*(V+be))/(t*V)),
          ('K24',(p*mu+Y*(V+T))/(V*(t*Z+E*Y)))]
    k=min(x for _,x in caps)
    jl=max((k-p)/X,(t*k-p)/Y)
    g=(t*k-1-Y*jl)/V
    return dict(k=k,j=jl,g=g,caps=caps,
                active=[n for n,x in caps if x==k])


def uniform_budgets(st):
    dd=derived(st);th,z=st.theta,st.primal
    de,ga,nu,ta,De,mu=[dd['cof'][n] for n in ['delta','gamma','nu','tau','Delta','mu']]
    t,E,be,X=th['t'],th['E'],th['beta'],th['X'];k,b,r,p=z['k'],z['b'],z['r'],z['p'];F=st.F
    Om=t*De+E*ta-mu;O,S,P=dd['O'],dd['S'],dd['P'];g=-z['v0'];j=-z['q0']
    j2=mu*(1+O[0][2])+De*(1-O[1][2])+ta*(1+O[2][2])
    rhs=ta*(F-4)+(De-ta)*(r-2)+Om*(k-b)+De*(1-O[1][0])+ta*(1+O[2][0])+j2
    require(mu*(1-O[0][0])==rhs,'V19 shared first-column slack identity')
    rr=(k-2)+(p-S[0][0])+X*(1+P[0])+(1+be-p)+(1-be)*(1-X)
    require(be*X*(1-g)==rr,'V19 receiver slack identity')
    lower=(1-X)*j+(1+P[0])+(1-be)*(1-g)
    require(O[0][0]-(k-2+be)==lower,'V19 first-entry lower decomposition')
    if F>4:
        require(O[0][0]<1 and g<1 and F+be<5,'strict global first-column budgets')
    if F>=H0:
        require(O[0][0]<Q(15,16) and g<Q(15,16),'uniform interior margins')
        require(be<Q(7,8) and de>Q(1,8),'uniform head guard')
    return dict(O00=O[0][0],g=g,first_margin=1-O[0][0],receiver_margin=1-g,
                beta=be,delta=de,shared_rhs=rhs)


def solve_frame(theta,verify=True):
    theta={n:rational(theta[n]) for n in PARAMS}
    d=v15.frame_data(theta)
    for name,ok in [('t>V',d['t']>d['V']),('Delta>tau',d['Delta']>d['tau']),
                    ('X>1/(1+beta)',d['X']>1/(1+d['beta'])),('zeta>0',d['zeta']>0)]:
        if not ok:return dict(status='BELOW_THRESHOLD',reason='inherited '+name)
    if d['nu']-d['E']*d['delta']<=0:return dict(status='BELOW_THRESHOLD',reason='inherited ell exclusion')
    p=(1+d['T'])/d['Z']
    if not p<1+d['beta']:return dict(status='BELOW_THRESHOLD',reason='inherited p ceiling')
    first=first_capacity_four(d,p)
    if first['k']<=2:return dict(status='BELOW_THRESHOLD',reason='four-capacity K<=2')
    middle=v15.middle_capacity(d,p,first['k'])
    if 2*middle['R']<H0:return dict(status='BELOW_THRESHOLD',reason='four-capacity middle ceiling')
    caps,td=budgets.six_budgets(d,first['k'],middle['R']);f=min(v for _,v in caps)
    out=dict(status='BELOW_THRESHOLD' if f<H0 else 'HIGH_MAXIMUM',p=p,first=first,middle=middle,
             caps=caps,tail=td,high_layer_bound=f,active=[n for n,v in caps if v==f])
    if f>=H0:
        # No old 12-capacity search is used to choose k, j or g.
        st,rec=budgets.reconstruct(d,theta,p,first,middle,f,td)
        if verify:check_state(st,'V19 four-capacity complete reconstruction')
        out.update(F=f,state=st,reconstruction=rec,interior=uniform_budgets(st))
    return out


def serial(x):
    if isinstance(x,Q):return str(x)
    if hasattr(x,'to_json'):return x.to_json()
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serial(v) for v in x]
    return x

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('input');ap.add_argument('--output');args=ap.parse_args()
    ob=json.load(open(args.input));ans=serial(solve_frame(ob.get('theta',ob)))
    if args.output:Path(args.output).write_text(json.dumps(ans,indent=2))
    print(json.dumps({k:v for k,v in ans.items() if k not in ['state','first','middle','tail']},indent=2))
