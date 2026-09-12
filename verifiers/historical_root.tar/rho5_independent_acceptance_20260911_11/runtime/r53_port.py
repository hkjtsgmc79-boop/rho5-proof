"""R53 read-only SAME-IMAGE R/D interval diagnostic; never a production terminal."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'v42'));import transport_box as tb
sys.path.insert(0,str(ROOT/'v43'));import local_guard as lg
I=tb.I;RHO=Q(3,1000);COSTS=(Q(13,4),Q(21),Q(28),Q(26))
def bilateral(z):
 r,s,t=z['r'],z['s'],z['t'];gap=(r-s).meet(I(0,r.hi));diff=(s-t).meet(I(0,r.hi))
 guard=2*s*diff-gap.sq()
 if s.lo<=0 or guard.lo<0:return None,{'status':'UNQUALIFIED_OR_UNRESOLVED','s':s.data(),'Q':guard.data(),'provably_Q_negative':guard.hi<0}
 a=(gap/(r+s)).meet(I(0,1));b=(2*s/(r+s)).meet(I(0,1)).meet(1-a)
 T=(a*(b*r+s)+b.sq()*t).meet(I(0,s.hi))
 T=T.meet(s-2*s*guard/((r+s).sq()))
 f=z['F'].meet(r+s*t/r);loss=(f*a.sq()).meet(I(0,max(Q(0),f.hi)))
 out={n:z[n]for n in tb.X_NAMES if n in z}
 out.update(r=s,w=-T,A=z['B'],B=b*z['A']-a*z['B'],c=z['c'],d=-a*z['c']-b*z['d'])
 for n in ('u','x'):
  out[n+'1']=z[n+'1'];out[n+'2']=-a*z[n+'1']-b*z[n+'2']
 for n in ('v','q'):out[n+'1']=z[n+'2'];out[n+'2']=b*z[n+'1']-a*z[n+'2']
 return out,{'status':'QUALIFIED','a':a.data(),'b':b.data(),'Q':guard.data(),'s':s.data(),'loss':loss.data(),'T':T.data()}
def centers():return [lg.chart_data(j,False)[0]for j in range(4)]
def measure(X,loss,route):
 cs=[]
 for j,cen in enumerate(centers()):
  ups=[(X[n]-c).abs_upper()for n,c in zip(tb.X_NAMES,cen)]
  lows=[max(Q(0),X[n].lo-c,c-X[n].hi)for n,c in zip(tb.X_NAMES,cen)]
  d=max(ups);dl=max(lows);score=d+COSTS[j]*loss.hi
  cs.append({'case':j,'distance_upper':str(d),'distance_lower':str(dl),'loss_upper':str(loss.hi),'cost':str(COSTS[j]),'score_upper':str(score),'accepted':score<=RHO,'cube_provably_disjoint':dl>RHO,'decisive_upper':tb.X_NAMES[ups.index(d)],'decisive_lower':tb.X_NAMES[lows.index(dl)],'V42_R_score_upper':str(d+tb.ONE_SLACK_COSTS[j]*loss.hi)if route=='R'else None,'V42_R_accepted':route=='R'and d+tb.ONE_SLACK_COSTS[j]*loss.hi<=tb.RHO})
 return cs

def check(box):
 z=tb.load_box(box);attempts=[]
 for tr,sg in product((False,True),product((-1,1),repeat=3)):
  src=tb.diagonal(tb.transpose(z)if tr else z,sg);branches=[]
  for sw,q in tb.ordered_branches(src):
   routes=[]
   for route in ('R','D'):
    try:
     if route=='R':
      X,parts=tb.target(q);loss=parts['loss'];meta={k:v.data()for k,v in parts.items()}
     else:
      X,meta=bilateral(q)
      if X is None:routes.append({'route':route,**meta});continue
      loss=I(*meta['loss'])
     cs=measure(X,loss,route);safe=loss.hi==0 or any(c['accepted']for c in cs)
     routes.append({'route':route,'status':'CONDITIONAL_ALPHA_SAFE'if safe else'OPEN','zero_loss':loss.hi==0,'source':{n:q[n].data()for n in tb.B_NAMES},'target':{n:X[n].data()for n in tb.X_NAMES},'quantities':meta,'centers':cs})
    except tb.Empty:
     # Not booked as empty: caller would still need a versioned root proof rule.
     routes.append({'route':route,'status':'EMPTY_ENCLOSURE_DIAGNOSTIC'})
   safe=any(v['status']=='CONDITIONAL_ALPHA_SAFE'for v in routes)
   branches.append({'swapped':sw,'status':'CONDITIONAL_ALPHA_SAFE'if safe else'OPEN','routes':routes})
  accepted=bool(branches)and all(b['status']=='CONDITIONAL_ALPHA_SAFE'for b in branches)
  attempts.append({'orientation':[tr,list(sg)],'branches':branches,'accepted_all_sorting_branches':accepted})
 candidates=[c for a in attempts for b in a['branches']for r in b['routes']for c in r.get('centers',[])]
 qualifiedD=sum(r['route']=='D'and 'centers'in r for a in attempts for b in a['branches']for r in b['routes'])
 Dtotal=sum(r['route']=='D'for a in attempts for b in a['branches']for r in b['routes'])
 return {'status':'CANDIDATE_REQUIRES_ROOT_RULE'if any(a['accepted_all_sorting_branches']for a in attempts)else'OPEN','attempts':attempts,'best_score_upper':min((c['score_upper']for c in candidates),key=Q)if candidates else None,'qualified_D_branches':qualifiedD,'D_branches':Dtotal,'all_evaluated_targets_provably_disjoint':bool(candidates)and all(c['cube_provably_disjoint']for c in candidates),'scope':'Only the specified representations and whole-branch qualified D targets; unqualified D subsets not excluded; actual root unchanged.'}
