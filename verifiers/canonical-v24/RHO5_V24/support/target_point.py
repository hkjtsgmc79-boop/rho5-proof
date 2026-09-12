"""V19 fixed-target/fixed-r endpoint test using exactly FOUR tail rows.

The general r existential quantifier is NOT searched here.  On gamma<=nu,
wall_decide below decides the entire head, using the new wall-representative
 theorem.  On gamma>nu, an empty wall is not reported as general emptiness.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import json,sys
from four_capacities import v15,budgets,first_capacity_four,uniform_budgets,serial
from model import rational,require,check_state
NAMES=('t','beta','V','T','X','Y','Z')


def target_point(head,target,r):
    th={n:rational(head[n]) for n in NAMES}; f=rational(target); x=rational(r)
    if not Q(33,8)<f<5: raise ValueError('require 33/8 < target < 5')
    if not f/2<=x<=Q(5,2):raise ValueError('r outside [target/2,5/2]')
    th.update(U=Q(1),E=Q(0));d=v15.frame_data(th)
    t,be,V,T,X,Y,Z=[th[n] for n in NAMES]
    de,ga,nu,ta,De,mu,qp,om0=[d[n] for n in ('delta','gamma','nu','tau','Delta','mu','Qp','Omega')]
    p=(1+T)/Z
    base=dict(head={n:th[n] for n in NAMES},target=f,r=x,gamma_minus_nu=ga-nu)
    if not(t>V and De>ta and X>1/(1+be) and p<1+be):
        return dict(base,status='POINT_EMPTY',reason='inherited head guard')
    y=f-x; b0=1+X;at=1-Y+ga*b0/de;ct=1+Z+nu*b0/de
    require(at<2<x and ct>2,'positive target denominators')
    cf=De*x+ta*y-(mu+De+ta)
    low=[('zero',Q(0)),('C0',(y-1-Z)/b0),
         ('oblique',(nu*(x-at)+qp*(y-ct))/(de*(x-at)))]
    emax=min(Q(1),nu/de);upper=[('Emax',emax)];rows={}
    # N/(A+B E): two stage lower bounds and two O10-based upper bounds.
    constants=[('K13',p*ga+X*(V+be),ga+be*t*X,Q(0)),
               ('K14',p*mu+X*(V+T),mu+X*T*t,X*V),
               ('K23',p*ga+Y*(V+be),t*V,Q(0)),
               ('K24',p*mu+Y*(V+T),V*t*Z,V*Y)]
    for name,N,A,B in constants:
        ar=ta*N-B*cf;br=A*cf-om0*N
        rows[name]=dict(a=ar,b=br,N=N,A=A,B=B)
        if ar>0:low.append((name,br/ar))
        elif ar<0:upper.append((name,br/ar))
        elif br>0:return dict(base,status='POINT_EMPTY',reason='zero coefficient '+name,rows=rows)
    which,e0=max(low,key=lambda nv:nv[1])
    base.update(E=e0,selector=which,lower_bounds=dict(low),upper_bounds=dict(upper),rows=rows)
    if e0>=emax:return dict(base,status='POINT_EMPTY',reason='strict Emax')
    for name,row in rows.items():
        if row['a']*e0<row['b']:
            return dict(base,status='POINT_EMPTY',reason='tail upper row '+name)
    th['E']=e0;d=v15.frame_data(th);first=first_capacity_four(d,p)
    if first['k']<=2:return dict(base,status='POINT_EMPTY',reason='four K<=2')
    middle=v15.middle_capacity(d,p,first['k']);base.update(K=first['k'],R=middle['R'])
    if middle['R']<x:return dict(base,status='POINT_EMPTY',reason='middle capacity at common least E')
    caps,td=budgets.six_budgets(d,first['k'],middle['R']);ff=min(v for _,v in caps)
    require(ff>=f,'feasible target point dominated by six budgets')
    # A wall target has an exact-height complete wall reconstruction.  For a
    # general point, reconstruct the maximum rather than a potentially
    # non-reconstructible non-extreme polygon point.
    actual=f if x==f/2 else ff
    st,rec=budgets.reconstruct(d,th,p,first,middle,actual,td)
    check_state(st,'V19 four-row target reconstruction');uniform_budgets(st)
    if x==f/2:require(st.primal['r']==x and st.primal['w']==-x,'wall target height')
    require(st.F>=f,'target witness height')
    return dict(base,status='POINT_SAT',state=st,reconstruction=rec,F=st.F)


def wall_decide(head,target):
    f=rational(target);ans=target_point(head,f,f/2)
    ans['status']='WALL_SAT' if ans['status']=='POINT_SAT' else 'WALL_EMPTY'
    return ans


def decide_head(head,target):
    ans=wall_decide(head,target)
    if ans['status']=='WALL_SAT':
        ans.update(wall_status=ans['status'],status='HEAD_SAT',scope='complete head')
    elif ans['gamma_minus_nu']<=0:
        ans.update(wall_status=ans['status'],status='HEAD_EMPTY',scope='complete head: gamma<=nu theorem')
    else:
        ans.update(wall_status=ans['status'],status='GENERAL_UNRESOLVED',scope='wall only; gamma>nu nonwall responsibility retained')
    return ans

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('head');ap.add_argument('target');ap.add_argument('--r');ap.add_argument('--wall-only',action='store_true');ap.add_argument('--output');args=ap.parse_args()
    obj=json.load(open(args.head));head=obj.get('head',obj.get('theta',obj))
    out=target_point(head,args.target,args.r) if args.r is not None else (wall_decide(head,args.target) if args.wall_only else decide_head(head,args.target))
    js=serial(out)
    if args.output:Path(args.output).write_text(json.dumps(js,indent=2)+'\n')
    print(json.dumps({k:v for k,v in js.items() if k not in ['state','rows','lower_bounds','upper_bounds','reconstruction']},indent=2))
