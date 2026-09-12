from pathlib import Path
from fractions import Fraction as Q
import json
from graph_protocol import *
from capacity import capacity,check_complete,encode
from interval_capacity import root_box

def run():
 src=json.loads((paths.ROOT/'inputs/evidence/capacity_controls.json').read_text())
 counter=0;boxes=0;exact_polynomials=0
 for old in src:
  f=[Q(x)for x in old['maximum']['frame']]
  if f[8]<0:f=f[:5]+[-x for x in f[5:]]
  out=capacity(f);assert out['status']=='COMPLETE_FIXED_FRAME_MAXIMUM'
  g=[Q(x)for x in out['point_gap']];check_complete(g);assert out['tail']['F']>GAMMA
  u,x,v,q=[f[i:i+3]for i in(5,8,11,14)]
  B,P,E=[out['prefix'][n]for n in('beta','p','e')]
  labels=exact_labels(u,x,v,q,B,P,E);assert labels
  aux=[g[0],g[1],g[1]-g[22],g[1]-g[23],*g[3:22],out['tail']['F']]
  assert len(aux)==24
  for lab in labels:
   for _,p in CHARTS[lab][0]:assert eval_point(p,aux)>=0;exact_polynomials+=1
  for radius in(Q(0),Q(1,100000),Q(1,1000)):
   b=[]
   for value,rt in zip(f,root_box()):
    lo=max(rt.lo,value-radius);hi=min(rt.hi,value+radius)
    assert lo<=value<=hi;b.append(I(lo,hi))
   pa=parent_enclosure(b)
   assert pa['status']!='EMPTY'
   for lab in labels:
    z=contract_chart(pa,lab)
    assert z['status']=='BOUNDED',(lab,radius,z)
    assert all(Q(l)<=val<=Q(h) for val,(l,h)in zip(aux,z['aux_image'])),(lab,radius)
    boxes+=1
  counter+=1
 return {'complete_physical_canonical_controls':counter,'all_above_gamma':True,'exact_chart_polynomial_checks':exact_polynomials,'point_and_positive_width_chart_image_containment':boxes,'not_new_high_points':True}

if __name__=='__main__':print(json.dumps(run(),indent=2))
