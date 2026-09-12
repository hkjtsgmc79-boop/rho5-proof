"""V43: guard-preserving local X charts; exact rational acceptance only.

The imported polynomial source and center file are extracted from the received
B03 bytes. No production tree, cached enclosure or optimizer is used here.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path, PurePosixPath
from functools import lru_cache
import atexit,hashlib,json,sys,tempfile,zipfile
ROOT=Path(__file__).resolve().parent
RADIUS=Q(3,1000);GAIN=Q(1,16);SPEED=Q(9,4);COST=SPEED/GAIN
B_COSTS=(Q(13,4),Q(21),Q(28),Q(26))
PLUS_GAINS=(Q(49,100),Q(1,16),Q(2,25),Q(2,25))
PLUS_SPEEDS=(Q(25,16),Q(13,10),Q(89,40),Q(103,50))
ARCHIVE_SHA='a14a8a0f65ef15efba85493663b08d7517811f9cb48d6e22ff7e9bfc29df1b29'
class Rejected(ValueError):pass
def need(test,msg):
 if not test:raise Rejected(msg)
def jsonable(x):
 if isinstance(x,Q):return str(x)
 if isinstance(x,dict):return {str(k):jsonable(v)for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [jsonable(v)for v in x]
 return x
def hash_file(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
@lru_cache(None)
def source():
 arc=ROOT/'dependency/B_STRUCTURE_03_Exact_Package_2026-09-09.zip'
 need(hash_file(arc)==ARCHIVE_SHA,'B03 archive identity')
 td=tempfile.TemporaryDirectory(prefix='rho5_v43_source_');atexit.register(td.cleanup)
 with zipfile.ZipFile(arc)as z:
  for n in z.namelist():
   pp=PurePosixPath(n);need(not pp.is_absolute()and '..'not in pp.parts,'unsafe source path')
  z.extractall(td.name)
 base=Path(td.name)/'B_STRUCTURE_03';sys.path.insert(0,str(base))
 import b_structure_03 as b3
 data=json.loads((b3.DEP/'accepted_inputs/local_wall_certificate.json').read_text())
 return b3,data,td

def exact_q(x):
 need(isinstance(x,(str,int,Q))and not isinstance(x,bool),'exact rational input required')
 return Q(x)

def bounds(poly,cen,rho):
 b3,_,_=source();lm=b3.lm
 return b3.b02.qmin(poly,cen,rho),-b3.b02.qmin(lm.neg(poly),cen,rho)
def amp(poly,cen,rho):
 lo,hi=bounds(poly,cen,rho);return max(abs(lo),abs(hi))

def chart_data(case,swapped):
 b3,data,_=source();cs=data['cases'][case];act=cs['active_labels'][:]
 release={0:'P2+',2:'P2-'}
 need(not swapped or case in release,'invalid switched case')
 if swapped:act[act.index(release[case])]='P0-'
 return list(map(Q,cs['center'])),act,(release[case]if swapped else'P0-')

def check_chart(record):
 b3,_,_=source();lm=b3.lm;pol=lm.source();cols=[i for i,n in enumerate(lm.NAMES)if n!='p']
 need(set(record)=={'case','swapped','active_labels','preconditioner'},'chart schema')
 case=record['case'];sw=record['swapped']
 need(type(case)is int and 0<=case<4 and type(sw)is bool,'chart identity')
 cen,act,guard=chart_data(case,sw)
 need(record['active_labels']==act,'wrong replacement or coordinate labels')
 C=[[exact_q(v)for v in row]for row in record['preconditioner']]
 need(len(C)==21 and all(len(row)==21 for row in C),'21x21 preconditioner')
 J=[[lm.diff(pol[label],i)for i in cols]for label in act]
 E=[[lm.add(lm.const(int(i==j)),*[lm.scale(J[t][j],-C[i][t])for t in range(21)])for j in range(21)]for i in range(21)]
 need(all(lm.ev(p,cen)==0 for row in E for p in row),'not exact center inverse')
 q=max(sum(b3.affine_amp(p,cen,RADIUS)for p in row)for row in E)
 need(q<Q(1,5),'whole-cube inverse bound')
 inactive={n:b3.b02.qmin(p,cen,RADIUS)for n,p in pol.items()if n not in act and n!=guard}
 need(len(inactive)==78 and min(inactive.values())>Q(1,200),'other 78 physical inequalities')
 caps={n:bounds(pol[n],cen,RADIUS)[1]for n in ('O11+','O12+','O22-')}
 need(max(caps.values())<Q(1,40),'corner caps')
 gr=cols.index(1);gw=cols.index(2)
 wanted=['O22-']if sw and case==0 else['O12+']if sw else(['O12+']if case==0 else['O22-']if case==2 else['O12+','O22-'])
 directions=[]
 for label in wanted:
  v0=[row[act.index(label)]for row in C];n=max(map(abs,v0))
  Ev=[lm.add(*[lm.scale(row[j],v0[j])for j in range(21)])for row in E]
  approx=[lm.add(lm.const(v0[i]),Ev[i])for i in range(21)]
  rem=n*q*q/(1-q)
  speed=max(amp(p,cen,RADIUS)for p in approx)+rem
  gain=-bounds(lm.add(approx[gr],lm.neg(approx[gw])),cen,RADIUS)[1]-2*rem
  grad=[lm.diff(pol[guard],i)for i in cols]
  dot=lm.add(*[lm.mul(grad[i],approx[i])for i in range(21)])
  gradnorm=sum(amp(p,cen,RADIUS)for p in grad)
  lo,hi=bounds(dot,cen,RADIUS)
  increase=-hi-gradnorm*rem
  need(speed<SPEED and gain>GAIN,'positive ascent and speed bound')
  need(increase>(Q(2,5)if sw else Q(1,10)),'released/barrier guard is increasing')
  directions.append(dict(label=label,gain_lower=gain,speed_upper=speed,guard=guard,guard_derivative_lower=increase,neumann_remainder=rem))
 return dict(case=case,swapped=sw,qnorm=q,inactive_count=78,inactive_min_label=min(inactive,key=inactive.get),inactive_min=min(inactive.values()),caps=caps,directions=directions)

def verify_local(certificate=None):
 if certificate is None:certificate=json.loads((ROOT/'chart_certificate.json').read_text())
 need(set(certificate)=={'schema','radius','gain','speed','charts'},'certificate schema')
 need(certificate['schema']=='V43_P0_GUARD_PRESERVING_CHARTS_V1','certificate identity')
 for n,v in [('radius',RADIUS),('gain',GAIN),('speed',SPEED)]:need(exact_q(certificate[n])==v,'constant mismatch '+n)
 charts=certificate['charts'];need(len(charts)==6,'six charts')
 need([(r['case'],r['swapped'])for r in charts]==[(0,False),(0,True),(1,False),(2,False),(2,True),(3,False)],'chart coverage')
 results=[check_chart(r)for r in charts]
 single=[]
 for case in range(4):
  rr=next(r for r in results if r['case']==case and r['swapped']==(case==2))
  dd=next(d for d in rr['directions']if d['label']=='O12+')
  need(dd['gain_lower']>PLUS_GAINS[case] and dd['speed_upper']<PLUS_SPEEDS[case],'single slack rational constants')
  need(PLUS_SPEEDS[case]<B_COSTS[case]*PLUS_GAINS[case],'single slack displacement cost')
  single.append(dict(case=case,gain=PLUS_GAINS[case],speed=PLUS_SPEEDS[case],cost=B_COSTS[case]))
 need(max(B_COSTS)/Q(84,5)*Q(3,2500)==Q(1,500)<RADIUS,'strong B03 inclusion')
 need(2*RADIUS<min(PLUS_GAINS),'R single-corner resource')
 # Closed old entrance is strictly within the new guard-preserving domain.
 need(COST/Q(84,5)*Q(3,2500)==Q(9,3500)<RADIUS,'B03 inclusion arithmetic')
 # R and D have enough of the same target corner slacks for restoration.
 need(RADIUS<GAIN,'single-sided slack budget')
 need(Q(1,40)/(2-Q(1,40))==Q(1,79),'bilateral a bound')
 need(Q(9,2)/(1-Q(1,79)**2)<5,'bilateral source F bound')
 need(Q(80,79)<Q(79,40),'bilateral slack payment')
 b3,data,_=source()
 need(all(Q(c['center'][1])+Q(c['center'][2])==0 for c in data['cases']),'centers have zero diagonal gap')
 need(all(2*Q(c['center'][1])+2*RADIUS<Q(9,2)for c in data['cases']),'local FX bound')
 return dict(status='V43_SIX_CHARTS_EIGHT_INWARD_DIRECTIONS_PASS',radius=RADIUS,gain=GAIN,speed=SPEED,cost=COST,charts=results,single_slack=single)

def point_entry(target,loss,case):
 """Arithmetic entrance only. Caller MUST certify actual physical X and same-source loss."""
 b3,_,_=source();need(type(case)is int and 0<=case<4,'case')
 z=[exact_q(x)for x in target];need(len(z)==22,'X22 order')
 ell=exact_q(loss);need(ell>=0,'nonnegative actual loss')
 cen,_,_=chart_data(case,False);d=max(abs(x-y)for x,y in zip(z,cen))
 hp=b3.lm.ev(b3.lm.source()['O12+'],z)
 S=hp+b3.lm.ev(b3.lm.source()['O22-'],z)
 need(min(b3.lm.ev(p,z)for p in b3.lm.source().values())>=0,'actual physical X input')
 cost=B_COSTS[case]
 accepted=(d+cost*ell<=RADIUS and ell<=hp*PLUS_GAINS[case])
 return dict(accepted=accepted,distance=d,loss=ell,h_plus=hp,slack_sum=S,cost=cost,score=d+cost*ell,margin=RADIUS-d-cost*ell)

if __name__=='__main__':print(json.dumps(jsonable(verify_local()),indent=2))
