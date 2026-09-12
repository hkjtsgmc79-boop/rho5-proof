"""V24: exact fixed-seven-head target test in the layer f >= 1653/400.

E is quantified out: its least feasible value must equal L_D.  The first
capacity must be uniquely K24.  No beta scan and no floating input are used.
"""
from __future__ import annotations
from pathlib import Path
from fractions import Fraction as Q
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent/'support'))
from model import State,rational,check_state,require,derived
import v15_capacities as original
from four_capacities import serial
NAMES=('t','beta','V','T','X','Y','Z')
CUT=Q(1653,400)

def decide(head,target):
    th={n:rational(head[n]) for n in NAMES};f=rational(target)
    if not CUT<=f<5:raise ValueError('V24 target must satisfy 1653/400 <= f < 5')
    t,be,V,T,X,Y,Z=(th[n]for n in NAMES)
    if not(0<t<=1 and 0<V<1 and all(0<x<=1 for x in (be,T,X,Y,Z))):
        raise ValueError('input outside the declared positive outer box')
    th.update(U=Q(1),E=Q(0));data=original.frame_data(th)
    de,ga,nu,ta,De,mu,qp,om0=(data[n]for n in ('delta','gamma','nu','tau','Delta','mu','Qp','Omega'))
    r=f/2;p=(1+T)/Z;s=p-1;d=t*X-Y;b0=1+X
    ans=dict(head={n:th[n]for n in NAMES},target=f,scope='fixed seven-parameter head; all E and inner variables')
    def empty(reason):return dict(ans,status='HEAD_EMPTY',reason=reason)
    if not(t>V and De>ta and X>1/(1+be) and p<1+be and f+be<5):return empty('inherited high head guard')
    if not(d>0 and t*p+d-1>0 and 1+t+d<Q(33,16)):return empty('V22 geometric guard')
    at=1-Y+ga*b0/de;ct=1+Z+nu*b0/de
    require(at<2<r and ct>2,'positive oblique denominator')
    E=(nu*(r-at)+qp*(r-ct))/(de*(r-at));LC=(r-1-Z)/b0
    ans.update(E=E,LC=LC,selector='L_D only')
    if not(E>LC and E<1 and nu-de*E>0):return empty('oblique E domain')
    th['E']=E;data=original.frame_data(th)
    k=(p*mu+Y*(V+T))/(V*(t*Z+E*Y))
    other={'K13':(p*ga+X*(V+be))/(ga+be*t*X),
           'K14':(p*mu+X*(V+T))/(mu+X*(V*E+T*t)),
           'K23':(p*ga+Y*(V+be))/(t*V)}
    ans.update(k=k,other_first_capacities=other)
    if not(k>2 and all(k<v for v in other.values())):return empty('unique K24 qualification')
    b=de*(r-at)/qp
    if not(b0<b<=k):return empty('tail core interval')
    A1=1+Y+t*(1-X);B1=qp;C1=1+Y+t*(p-X);D1=ga+t*be*X
    A2=(t*(1+Z)+E*(1+Y))/(t+E);B2=(t*nu-E*ga)/(t+E)
    C2=(t*k+E*(1+Y))/(t+E);D2=E*ga/(t+E)
    require(B1>0 and B2>0,'positive middle slope')
    caps={'I2H':A2+B2*s/be,'R11':A1+qp*s,'R21':(B2*C1+D1*A2)/(B2+D1),
          'R12K24':(B1*C2+D2*A1)/(B1+D2),'R22K24':(B2*C2+D2*A2)/(B2+D2)}
    ans['five_middle_capacities']=caps
    if any(x<r for x in caps.values()):return empty('five common middle budgets')
    j=(t*k-p)/Y;g=s/V
    h=max(Q(0),(r-A1)/B1,(r-A2)/B2);a=(r-1-Y+ga*h)/t
    v=(b-b0)/de;q=1-be*v
    st=State(th,dict(k=k,a=a,b=b,r=r,w=-r,p=p,e=Q(1),v0=-g,q0=-j,v1=h,q1=-1-be*h,v2=v,q2=q))
    dd=check_state(st,'V24 canonical exact wall target')
    require(st.F==f and dd['P'][2]==1 and dd['O'][0][2]==-1 and dd['O'][1][2]==1 and dd['O'][2][2]==-1,'joint tail contacts')
    require(dd['S'][0][0]<p and dd['P'][0]>-1 and dd['S'][1][0]==p and dd['O'][2][0]==-1,'strict first-column rigidity')
    # An independent full twelve-capacity check is a regression assertion,
    # not the algorithm used to choose k or a separate-column completion.
    old=original.first_capacity(data,p)
    require(old['k']==k,'original twelve-capacity recovery')
    ans.update(status='HEAD_SAT',state=st,F=f,
               strict_first_slacks={'p-S00':p-dd['S'][0][0],'1+P0':1+dd['P'][0]})
    return ans

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('head');p.add_argument('target');p.add_argument('--output');a=p.parse_args()
    x=json.load(open(a.head));result=serial(decide(x.get('head',x.get('theta',x)),a.target))
    text=json.dumps(result,indent=2)
    if a.output:Path(a.output).write_text(text+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='state'},indent=2))
