"""Full rational physical controls at P0=0, never used as a domain proof."""
from fractions import Fraction as Q
from pathlib import Path
import json
import local_guard as g

def solve(A,b):
    n=len(A);T=[list(row)+[v]for row,v in zip(A,b)]
    for j in range(n):
        pivot=next((i for i in range(j,n)if T[i][j]),None)
        g.need(pivot is not None,'singular exact control Jacobian')
        T[j],T[pivot]=T[pivot],T[j];d=T[j][j];T[j]=[v/d for v in T[j]]
        for i in range(n):
            if i!=j and T[i][j]:
                t=T[i][j];T[i]=[a-t*b for a,b in zip(T[i],T[j])]
    return [row[-1]for row in T]
def cp(M):
    g.need(len(M)==5 and all(len(row)==5 for row in M),'5x5')
    T=M;piv=[];tails=[]
    for step in range(5):
        p=T[0][0];g.need(p!=0,'nonzero pivot');piv.append(p);tails.append(T)
        g.need(all(abs(v)<=abs(p)for row in T for v in row),'full CP at step '+str(step))
        T=[[T[i][j]-T[i][0]*T[0][j]/p for j in range(1,len(T))]for i in range(1,len(T))]
    return piv,tails

def verify():
    b3,data,_=g.source();lm=b3.lm;pol=lm.source();cols=[i for i,n in enumerate(lm.NAMES)if n!='p']
    out=[]
    for rec in json.loads((g.ROOT/'controls/boundary_controls.json').read_text()):
        case=rec['case'];z=list(map(Q,rec['z']));M=[[Q(v)for v in row]for row in rec['matrix']]
        g.need(M==b3.b02.matrix(dict(zip(lm.NAMES,z))),'independent matrix reconstruction')
        piv,tails=cp(M);g.need(piv==list(map(Q,rec['pivots'])),'stored pivots')
        g.need(tails[3]==[[z[1],z[1]],[z[1],z[2]]],'actual X tail')
        slacks={n:lm.ev(p,z)for n,p in pol.items()}
        g.need(slacks['P0-']==0 and all(v>0 for n,v in slacks.items()if n!='P0-'),'exact active boundary and all other slacks positive')
        g.need({n:str(v)for n,v in slacks.items()}==rec['all_slacks'],'stored slack table')
        center,act,unused=g.chart_data(case,False);d=max(abs(a-b)for a,b in zip(z,center))
        g.need(Q(3,2500)<d<g.RADIUS,'outside old, inside new cube')
        lab='O22-'if case==0 else'O12+';guard='P2+'if case==0 else'P2-'
        slopes=[];vectors=[]
        for switched in (False,True):
            _,active,_=g.chart_data(case,switched)
            J=[[lm.ev(lm.diff(pol[n],i),z)for i in cols]for n in active]
            rhs=[-Q(int(n==lab))for n in active]
            v=solve(J,rhs);vectors.append(v)
            gain=v[cols.index(1)]-v[cols.index(2)]
            P0dot=sum(lm.ev(lm.diff(pol['P0-'],i),z)*v[j]for j,i in enumerate(cols))
            freedot=sum(lm.ev(lm.diff(pol[guard],i),z)*v[j]for j,i in enumerate(cols))
            g.need(gain>0,'control ascent')
            if switched:g.need(P0dot==0 and freedot>0,'switched guard tangent and released band increasing')
            else:g.need(P0dot<0,'old risky direction exits physical domain at the boundary')
            slopes.append(dict(switched=switched,height_derivative=gain,P0_derivative=P0dot,released_guard=guard,released_derivative=freedot))
        oldJ=[[lm.ev(lm.diff(pol[n],i),z)for i in cols]for n in act]
        tangent=solve(oldJ,[Q(int(n==guard))for n in act])
        gradP=[lm.ev(lm.diff(pol['P0-'],i),z)for i in cols]
        denom=sum(a*b for a,b in zip(gradP,tangent))
        numer=sum(a*b for a,b in zip(gradP,vectors[0]))
        g.need(denom!=0,'coordinate-change denominator')
        g.need(vectors[1]==[a-b*numer/denom for a,b in zip(vectors[0],tangent)],'rank-one coordinate-change identity at full control')
        out.append(dict(case=case,distance=d,F=-piv[-1],P0=slacks['P0-'],directions=slopes))
    rec=json.loads((g.ROOT/'controls/proper_B_boundary.json').read_text())
    raw={n:Q(v)for n,v in rec['raw_point'].items()};can=b3.b02.normalize_v37(raw)
    g.need({n:str(v)for n,v in can.items()}==rec['canonical_point'],'same-frame V37 canonical maximum')
    M=b3.b02.matrix(can);g.need(M==[[Q(v)for v in row]for row in rec['matrix']],'canonical matrix bytes')
    piv,tails=cp(M);r,s,t=can['r'],can['s'],can['t']
    g.need(tails[3]==[[r,s],[t,-r]] and 0<s<r and 0<t<r,'actual proper negative-D tail')
    F=r+s*t/r;g.need(-piv[-1]==F and Q(4)<F<Q(4132517,10**6),'control height, not gamma-high credit')
    g.need(1+can['q0']+can['beta']*can['v0']==0,'canonical P0 boundary')
    centers=[list(map(Q,c['center']))for c in data['cases']]
    pdiff=min(abs(can['p']-c[7])for c in centers)
    g.need(pdiff>Q(3,2500),'all old B03 routes fail by p-invariance')
    measurements=b3.orbit_measurements(M,centers)
    candidates=measurements['candidates'];pick=rec['measurement']
    matches=[m for m in candidates if (m['route'],m['transpose'],tuple(m['signs']),m['case'])==(pick['route'],pick['transpose'],tuple(pick['signs']),pick['case'])]
    g.need(len(matches)==1 and g.jsonable(matches[0])==pick,'actual single source and target')
    m=matches[0];entry=g.point_entry(m['target_coordinates'],m['loss'],m['case'])
    g.need(entry['accepted'] and g.jsonable(entry)==rec['new_entry'],'strictly new guard-preserving entrance')
    xt=list(map(Q,m['target_coordinates']));g.need(lm.ev(pol['P0-'],xt)==0,'actual transported X also starts on P0=0')
    cp(b3.b02.matrix(dict(zip(lm.NAMES,xt))))
    # Nonzero left/right packet minors, recorded explicitly; no macro-flag claim.
    u=[can['u'+str(i)]for i in range(3)];x=[can['x'+str(i)]for i in range(3)]
    v=[can['v'+str(i)]for i in range(3)];q=[can['q'+str(i)]for i in range(3)]
    minorsL=[u[i]*x[j]-u[j]*x[i]for i in range(3)for j in range(i+1,3)]
    minorsR=[v[i]*q[j]-v[j]*q[i]for i in range(3)for j in range(i+1,3)]
    g.need(any(minorsL)and any(minorsR),'both actual packets rank2')
    k=can['k'];aa=can['A']/k;bb=can['B']/k;cc=can['c'];dd=can['d'];rr=r/k;ss=s/k;tt=t/k;ww=-rr
    flag_rows={'RL':[rr*aa*cc,tt*aa*dd,rr*tt*cc*dd,-rr*tt*u[1]*u[2]],
      'SL':[ss*bb*cc,ww*bb*dd,ss*ww*cc*dd,-ss*ww*u[1]*u[2]],
      'RR':[rr*aa*cc,ss*bb*cc,rr*ss*aa*bb,-rr*ss*v[1]*v[2]],
      'SR':[tt*aa*dd,ww*bb*dd,tt*ww*aa*bb,-tt*ww*v[1]*v[2]]}
    flags={n:all(x>=0 for x in row)for n,row in flag_rows.items()}
    g.need(not any(flags.values()),'proper B failure flags')
    return dict(status='V43_EXACT_P0_BOUNDARY_CONTROLS_PASS',X_boundary_controls=out,
      proper_B=dict(F=F,P0=Q(0),minimum_p_distance=pdiff,transported_P0=Q(0),left_minors=minorsL,right_minors=minorsR,
      route=m['route'],case=m['case'],entry=entry,flags=flags),new_gamma_high_control=False)
if __name__=='__main__':print(json.dumps(g.jsonable(verify()),indent=2))
