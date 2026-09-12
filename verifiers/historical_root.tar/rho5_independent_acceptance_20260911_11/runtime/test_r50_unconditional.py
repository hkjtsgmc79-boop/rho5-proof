from r50_protocol import *
import r50_unconditional as u
from capacity import capacity,check_complete
from interval_capacity import root_box
Q=old.Q
def main():
 controls=json.loads((ROOT/'v39/inputs/evidence/capacity_controls.json').read_text());checks=0
 for source in controls:
  f=list(map(Q,source['maximum']['frame']))
  if f[8]<0:f=f[:5]+[-v for v in f[5:]]
  result=capacity(f);assert result['status']=='COMPLETE_FIXED_FRAME_MAXIMUM'
  gap=list(map(Q,result['point_gap']));check_complete(gap);assert result['tail']['F']>gp.GAMMA
  aux=[gap[0],gap[1],gap[1]-gap[22],gap[1]-gap[23],*gap[3:22],result['tail']['F']]
  for radius in (Q(0),Q(1,100000),Q(1,1000)):
   box=[[str(max(rt.lo,z-radius)),str(min(rt.hi,z+radius))]for z,rt in zip(f,root_box())]
   out=u.contract(box);assert out['status']=='BOUNDED'
   assert all(Q(lo)<=z<=Q(hi)for z,(lo,hi)in zip(aux,out['aux_image']))
   checks+=1
 tests=0
 for proof in ({'kind':'I'},{'kind':'C','weights':[[0,1]]},{'kind':'C','weights':[[0,-1]]},{'kind':'Z'}):
  try:u.verify(box,u.wrap(box,proof))
  except (ValueError,AssertionError):tests+=1
  else:raise AssertionError('false U40 certificate accepted')
 print(json.dumps({'status':'U40_UNIVERSAL_FULL_CONTROLS_PASS','actual_high_controls':len(controls),'point_and_width_containment':checks,'negative_controls':tests,'no_conditional_contact_added':True}))
if __name__=='__main__':main()
