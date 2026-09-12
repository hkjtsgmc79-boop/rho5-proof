#!/usr/bin/env python3
"""Independent rational check of the diagnostic height witnesses, no tree credit."""
from pathlib import Path
from fractions import Fraction as Q
import json
own=Path('/root/microscope_ws/rho5_cqg_v35_low_alpha_20260908/attempt_01')
root=own/'working_flow_tube';probe=own/'weighted_alpha_probe'
model=json.loads((root/'models/II_LOW_ALPHA/model.json').read_text())
alpha=Q(json.loads((root/'alpha.json').read_text())['isolating_interval']['lower'])
samples={j['id']:j for j in json.loads((probe/'SAMPLES.json').read_text())['jobs']}
rows=[json.loads(s) for s in (probe/'RESULTS.jsonl').read_text().splitlines()]
unit=model['root_denominator']*2**128;native=len(model['variables']);total=native+len(model['pairs'])
verified=[]
for result in rows:
 t=result['height_t']
 if not t:continue
 j=samples[result['id']];lo=[Q(x,unit) for x in j['lo']];hi=[Q(x,unit) for x in j['hi']]
 for i,k in model['pairs']:
  products=[lo[i]*lo[k],lo[i]*hi[k],hi[i]*lo[k],hi[i]*hi[k]]
  lo.append(min(products));hi.append(max(products))
 co=[Q(0)]*total;rhs=Q(0);seen=set()
 for row,w in result['weights']:
  assert w>0 and row not in seen;seen.add(row)
  if row<len(model['rows']):
   data=model['rows'][row]
   for k,a in enumerate(data['coefficients']):co[k]+=w*a
   rhs+=w*data['rhs']
  else:
   pair,side=divmod(row-len(model['rows']),4);i,k=model['pairs'][pair];y=native+pair
   if side==0:ci,ck,cy,b=lo[k],lo[i],-1,lo[i]*lo[k]
   elif side==1:ci,ck,cy,b=hi[k],hi[i],-1,hi[i]*hi[k]
   elif side==2:ci,ck,cy,b=-hi[k],-lo[i],1,-lo[i]*hi[k]
   else:ci,ck,cy,b=-lo[k],-hi[i],1,-hi[i]*lo[k]
   co[i]+=w*ci;co[k]+=w*ck;co[y]+=w*cy;rhs+=w*b
 co[1]-=t;co[2]+=t
 bound=rhs-sum(min(a*l,a*h) for a,l,h in zip(co,lo,hi))
 assert bound<=t*alpha
 cpp_scaled=(bound-t*alpha)*alpha.denominator*unit**2
 assert cpp_scaled.denominator==1 and cpp_scaled.numerator==int(result['margin'])
 verified.append({'id':result['id'],'height_upper_exact':str(bound/t),
                  'alpha_lower_gap_exact':str(alpha-bound/t),'new_candidate':not result['closed_contradiction']})
assert len(verified)==3 and sum(r['new_candidate'] for r in verified)==2
answer={'status':'INDEPENDENT_FRACTION_DIAGNOSTIC_CHECK_PASSED','witnesses':verified,
        'production_acceptor_changed':False,'original_root_proof_credit':0}
(own/'WEIGHTED_ALPHA_FRACTION_CHECK.json').write_text(json.dumps(answer,indent=2)+'\n')
print(json.dumps({'status':answer['status'],'checked':len(verified),'original_root_proof_credit':0}))
