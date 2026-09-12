"""Exact rational certificate for a physical wall-reaching flow. No floating point.
The proof of existence/continuation and inference F<=alpha-c*(r+w) is in THEORY.md.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,time
from local_model import *
ROOT=Path(__file__).parent

def box_min_quadratic(poly,cen,rho):
 # Exact degree-two Taylor expansion; rigorous on every real point of the cube.
 assert all(len(m)<=2 for m in poly)
 lin=sum((abs(ev(diff(poly,i),cen)) for i in range(len(cen))),Q(0))
 quad=sum((abs(v) for m,v in poly.items() if len(m)==2),Q(0))
 return ev(poly,cen)-rho*lin-rho*rho*quad

def verify(data):
 assert data['schema']=='V35_LOCAL_WALL_FLOW_V1'
 assert data['coordinate_order']==list(NAMES) and data['fixed_coordinate']=='p'
 inner,outer=Q(data['inner_radius']),Q(data['outer_radius']);speed=Q(data['uniform_speed_cap']);gain=Q(data['uniform_height_gain'])
 assert 0<inner<outer and speed>0 and gain>0
 allpoly=source();cols=[i for i,n in enumerate(NAMES) if n!='p'];results=[]
 assert [v['case'] for v in data['cases']]==list(range(4))
 for case in data['cases']:
  num=case['case'];cen=list(map(Q,case['center']));C=[list(map(Q,row)) for row in case['inverse_preconditioner']];act=case['active_labels']
  assert len(cen)==22 and len(C)==21 and all(len(row)==21 for row in C)
  assert len(act)==21 and len(set(act))==21 and 'r+w' in act and all(n in allpoly for n in act)
  assert cen[1]+cen[2]==0
  J=[[diff(allpoly[n],i) for i in cols] for n in act]
  qnorm=Q(0)
  for i in range(21):
   row_sum=Q(0)
   for j in range(21):
    err=add(const(int(i==j)),*[scale(J[t][j],-C[i][t]) for t in range(21)])
    assert all(len(m)<=1 for m in err)
    bound=abs(ev(err,cen))+outer*sum((abs(c) for m,c in err.items() if m),Q(0))
    row_sum+=bound
   qnorm=max(qnorm,row_sum)
  assert qnorm<Q(1,25),('inverse contraction not certified',num,float(qnorm))
  col=act.index('r+w');v=[row[col] for row in C];nv=max(map(abs,v));err=qnorm*nv/(1-qnorm)
  norm_cap=nv/(1-qnorm);fderiv=v[cols.index(1)]-v[cols.index(2)]+2*err
  assert norm_cap<speed,('speed',num,float(norm_cap))
  assert fderiv<=-gain,('height slope',num,float(fderiv))
  assert 2*inner*speed<outer-inner,('cannot continue to wall',num)
  inactive={n:box_min_quadratic(poly,cen,outer) for n,poly in allpoly.items() if n not in act}
  assert all(v>0 for v in inactive.values()),('inactive negative',num,[(n,float(v)) for n,v in inactive.items() if v<=0])
  # All endpoint R0 requirements are checked uniformly. Signed permutations preserve cube widths.
  endcen=wall_transform(cen,num)
  req={n:box_min_quadratic(poly,endcen,outer) for n,poly in canonical_requirements().items()}
  assert all(v>0 for v in req.values()),('bad R0 endpoint',num,req)
  # Low-r and remaining band are not needed to prove safety, but verify locality for task routing.
  assert cen[0]-outer>2 and cen[0]+outer<Q(21,10)
  assert cen[0]-cen[1]-2*outer>0
  results.append({'case':num,'qnorm':str(qnorm),'qnorm_display':float(qnorm),'speed_bound':str(norm_cap),'speed_display':float(norm_cap),'height_derivative_upper':str(fderiv),'height_derivative_display':float(fderiv),'minimum_inactive_slack':str(min(inactive.values())),'minimum_inactive_display':float(min(inactive.values())),'minimum_R0_guard':str(min(req.values())),'inactive_count':len(inactive),'endpoint_guard_count':len(req)})
 return {'status':'V35_FOUR_COMPLETE_LOCAL_WALL_FLOWS_CERTIFIED','cases':results,'F_bound':f'F <= alpha - ({gain})*(r+w)','inner_radius':str(inner),'outer_radius':str(outer),'strict_macro_ledger':'11/15','global_coverage_proved':False}
if __name__=='__main__':
 start=time.time();result=verify(json.loads((ROOT/'local_wall_certificate.json').read_text()));result['seconds']=time.time()-start
 print(json.dumps(result,indent=2))
