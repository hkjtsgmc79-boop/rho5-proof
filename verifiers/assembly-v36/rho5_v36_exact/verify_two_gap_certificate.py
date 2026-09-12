"""Whole-box exact rational certificate. Analytic continuation is proved in THEORY.md."""
from pathlib import Path
from fractions import Fraction as Q
import json,time
from gap_model import NAMES,source,add,const,scale,ev,diff
ROOT=Path(__file__).parent

def box_min(poly,cen,R):
 assert all(len(m)<=2 for m in poly)
 return ev(poly,cen)-R*sum(abs(ev(diff(poly,i),cen)) for i in range(len(cen)))-R*R*sum(abs(v)for m,v in poly.items()if len(m)==2)

def verify(cert):
 assert cert['schema']=='V36_TWO_GAP_FLOW_V1'
 assert cert['coordinate_order']==list(NAMES) and cert['fixed_coordinate']=='p'
 outer=Q(cert['outer_radius']);inner=Q(cert['inner_radius']);speed=Q(cert['speed_cap']);gain=Q(cert['gain'])
 assert outer==Q(1,1250) and inner==Q(1,10000) and speed==3 and gain==Q(1,10)
 assert inner+speed*2*inner<outer
 rows=source();cols=[i for i,n in enumerate(NAMES) if n!='p'];result=[]
 assert [c['case']for c in cert['cases']]==[0,1,2,3]
 for case in cert['cases']:
  cen=list(map(Q,case['center']));C=[list(map(Q,row))for row in case['preconditioner']];active=case['active_labels']
  assert len(cen)==24 and cen[22:]==[0,0] and cen[1]+cen[2]==0
  assert len(C)==23 and all(len(row)==23 for row in C)
  assert len(active)==23 and len(set(active))==23
  assert active[-2:]==['sigma','tau'] and 'r+w' in active
  assert all(a in rows for a in active)
  J=[[diff(rows[n],i)for i in cols]for n in active]
  norm=Q(0)
  for i in range(23):
   rs=Q(0)
   for j in range(23):
    err=add(const(int(i==j)),*[scale(J[t][j],-C[i][t])for t in range(23)])
    assert all(len(m)<=1 for m in err)
    rs+=abs(ev(err,cen))+outer*sum(abs(v) for m,v in err.items()if m)
   norm=max(norm,rs)
  assert norm<Q(1,25),(case['case'],'contraction',float(norm))
  directions={};rmin=cen[1]-outer;assert rmin>0
  # For exact inverse directions, sigma/tau equations force dsigma,dtau to (1,0)/(0,1).
  # F=r-w-sigma-tau+sigma*tau/r. Bound both perturbations globally on outer cube.
  for g in ('sigma','tau'):
   v=[row[active.index(g)]for row in C];nv=max(map(abs,v));error=norm*nv/(1-norm);cap=nv/(1-norm)
   upper=v[cols.index(1)]-v[cols.index(2)]-1+2*error+outer/rmin+outer**2*cap/rmin**2
   assert cap<speed,(case['case'],g,'speed',float(cap))
   assert upper<=-gain,(case['case'],g,'gain',float(upper))
   directions[g]={'speed_bound':str(cap),'speed_display':float(cap),'height_derivative_upper':str(upper),'derivative_display':float(upper)}
  inactive={n:box_min(p,cen,outer)for n,p in rows.items()if n not in active}
  assert all(v>0 for v in inactive.values()),(case['case'],[(n,float(v))for n,v in inactive.items()if v<=0])
  result.append({'case':case['case'],'inverse_contraction':str(norm),'contraction_display':float(norm),'directions':directions,'unselected_slacks':len(inactive),'minimum_unselected_slack':str(min(inactive.values())),'minimum_display':float(min(inactive.values()))})
 return {'status':'V36_FOUR_COMPLETE_TWO_GAP_FLOW_CERTIFICATES_PASS','source_variables':24,'jacobian_dimension':23,'outer_radius':str(outer),'gain':str(gain),'cases':result,'result':'F<=alpha-(sigma+tau)/10','input_theorem':'complete_X_alpha','global_proper_B_coverage':False}

if __name__=='__main__':
 start=time.monotonic();c=json.loads((ROOT/'two_gap_certificate.json').read_text());out=verify(c);out['seconds']=time.monotonic()-start
 (ROOT/'evidence/two_gap_verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
