"""Independent actual-matrix checks for the new interval interface.
Finite controls check code; theorems carry the all-real quantifiers.
"""
from pathlib import Path
from fractions import Fraction as Q
import copy,itertools,json
from _v42_bootstrap import ROOT,prepare,b02_api,centers,sha
import transport_box as tb

def matrix(z):
 k,r,s,t,A,B,c,d,p,e,beta=[z[n]for n in tb.B_NAMES[:11]]
 u=[z[f'u{i}']for i in range(3)];x=[z[f'x{i}']for i in range(3)];v=[z[f'v{i}']for i in range(3)];q=[z[f'q{i}']for i in range(3)]
 D=[[k,A,B],[c*k,r+c*A,s+c*B],[d*k,t+d*A,-r+d*B]]
 O=[[D[i][j]+x[i]*q[j]+u[i]*v[j]for j in range(3)]for i in range(3)]
 return [[Q(1),-e]+v,[beta,p-e*beta]+[q[j]+beta*v[j]for j in range(3)]]+[[u[i],p*x[i]-e*u[i]]+O[i]for i in range(3)]

def run():
 b02=b02_api();b01=b02.b01;cen=centers();cc=[list(map(Q,c))for c in cen]
 records=json.loads((prepare()['b02']/'data/PHYSICAL_HIGH_CONTROLS16.json').read_text())['cases']
 counts={'controls':0,'old_literal':0,'new_literal':0,'old_finite_operations':0,'new_finite_operations':0,'target_coordinates':0,'symmetry_coordinates':0,'wide_containment_checks':0,'sorting_boundary_points':0}
 for rec in records:
  z,M,_,_=b01.source_quantities(rec);z['F']=z['r']+z['s']*z['t']/z['r']
  box=[[str(z[n])]*2 for n in tb.B_NAMES];zz=tb.load_box(box)
  old=tb.check_box(box,cen,False,'legacy');new=tb.check_box(box,cen,False,'one_slack')
  actual=b02.target_measurements(M,cc)
  if (old['status']=='SAFE_ALPHA')!=actual['new_accepts']:raise AssertionError('Legacy reference')
  counts['controls']+=1;counts['old_literal']+=old['status']=='SAFE_ALPHA';counts['new_literal']+=new['status']=='SAFE_ALPHA'
  counts['old_finite_operations']+=tb.check_box(box,cen,True,'legacy')['status']=='SAFE_ALPHA'
  counts['new_finite_operations']+=tb.check_box(box,cen,True,'one_slack')['status']=='SAFE_ALPHA'
  ds=b02.native(actual['X_matrix'])
  ordered=next(src for sw,src in tb.ordered_branches(zz)if sw==(z['s']<z['t']))
  X,_=tb.target(ordered)
  for n in tb.X_NAMES:
   if not X[n].lo==X[n].hi==ds[n]:raise AssertionError('Point dictionary')
   counts['target_coordinates']+=1
  for tr,pv,sgn in itertools.product((False,True),(False,True),list(itertools.product((-1,1),repeat=3))):
   zt=tb.transpose(zz)if tr else zz;Mt=M
   if tr:
    J=b01.identity(5);J[1][1]=-1;Mt=b01.matmul(b01.matmul(J,b01.transpose(Mt)),J)
   if pv:
    zt=tb.opposite_pivot(zt);J=b01.embed([[Q(0),Q(-1)],[Q(1),Q(0)]]);Mt=b01.matmul(b01.matmul(J,Mt),J)
   zt=tb.diagonal(zt,sgn);aa,bb,cc0=sgn;J=b01.identity(5)
   for i,vv in enumerate((1,aa,bb,cc0,cc0)):J[i][i]=Q(vv)
   Mt=b01.matmul(b01.matmul(J,Mt),J);nt=b02.native(Mt);nt['F']=nt['r']+nt['s']*nt['t']/nt['r'];b01.cp_pivots(Mt)
   for n in tb.B_NAMES:
    if not zt[n].lo==zt[n].hi==nt[n]:raise AssertionError('Actual operation dictionary')
    counts['symmetry_coordinates']+=1
  # Widen all actual coordinates. Inclusion, not feasibility of every box point.
  wb=[[str(z[n]-Q(1,10**10)),str(z[n]+Q(1,10**10))]for n in tb.B_NAMES]
  swant=z['s']<z['t']
  for sw,src in tb.ordered_branches(tb.load_box(wb)):
   if sw!=swant:continue
   xt,qt=tb.target(src)
   for n in tb.X_NAMES:
    if not xt[n].lo<=ds[n]<=xt[n].hi:raise AssertionError('Whole-box image containment')
    counts['wide_containment_checks']+=1
 # Strict enlargement, including a positive-width all-physical-source box.
 w=json.loads((ROOT/'controls/one_slack_extension.json').read_text());M=[[Q(v)for v in row]for row in w['matrix']]
 z=b02.check_physical_B(M);a=b02.target_measurements(M,[list(map(Q,c))for c in cen])
 if not Q(4)<a['F']<tb.GAMMA:raise AssertionError('Control height scope')
 if not (0<z['s']<z['r'] and 0<z['t']<z['r']):raise AssertionError('Proper B extension control')
 new=tb.check_box(w['B24_box'],cen,False,'one_slack');old=tb.check_box(w['B24_box'],cen,True,'legacy')
 if new['status']!='SAFE_ALPHA'or old['status']!='OPEN':raise AssertionError('Positive-width domain comparison')
 for attempt in old['attempts']:
  for branch in attempt['branches']:
   if branch['status']=='EMPTY_BRANCH':continue
   losslo=Q(branch['common_quantities']['loss'][0])
   if any(Q(c['distance_lower'])+tb.COST*losslo<=tb.RHO for c in branch['centers']):raise AssertionError('Whole old finite-orbit domain exclusion')
 # Low physical symmetric source: equality and zero arms. Both sorting branches retained.
 z={n:Q(0)for n in tb.B_NAMES};z.update(k=Q(1,2),r=Q(1,10),p=Q(3,4),e=Q(1,4),beta=Q(1,2))
 for ss,tt in itertools.product((Q(0),Q(1,20),Q(1,10)),repeat=2):
  z['s'],z['t']=ss,tt;z['F']=z['r']+ss*tt/z['r'];M=matrix(z);b02.check_physical_B(M)
  actual=b02.target_measurements(M,[list(map(Q,c))for c in cen]);nt=b02.native(actual['X_matrix'])
  branches=list(tb.ordered_branches(tb.load_box([[str(z[n])]*2 for n in tb.B_NAMES])))
  if ss==tt and len(branches)!=2:raise AssertionError('Equality must retain both closed branches')
  for sw,src in branches:
   if sw!=(ss<tt)and ss!=tt:continue
   tx,_=tb.target(src)
   if sw==(ss<tt):
    for n in tb.X_NAMES:
     if not tx[n].lo<=nt[n]<=tx[n].hi:raise AssertionError('Boundary dictionary')
  counts['sorting_boundary_points']+=1
 z['s']=z['t']=Q(2,25);z['F']=z['r']+z['s']*z['t']/z['r'];b=[[str(z[n])]*2 for n in tb.B_NAMES]
 for ix in (2,3):b[ix]=[str(z[tb.B_NAMES[ix]]-Q(1,100000)),str(z[tb.B_NAMES[ix]]+Q(1,100000))]
 if len(list(tb.ordered_branches(tb.load_box(b))))!=2:raise AssertionError('Crossing chamber omitted')
 return {'status':'V42_PHYSICAL_PORT_CONTROLS_PASS',**counts,'positive_width_new_outside_legacy_32_operations':True,
         'extension_control_below_gamma':True,'supplied_high_control_families_not_population_estimate':True}
if __name__=='__main__':print(json.dumps(run()))
