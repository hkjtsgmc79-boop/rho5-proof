"""B14_SYMMETRY_ALPHA_V1, conditional on a proven complete physical source.
Do not install as an old V44 A/H terminal. This module returns alpha safety,
never gamma infeasibility. A source-bound caller must rebuild ancestors.
"""
from fractions import Fraction as Q
import hashlib,json
import structural_rules as sr
from transport_local import sorted_branches,sorted_R,KAPPA
RULE='B14_SYMMETRY_ALPHA_V1'
RADIUS=Q(3,1000)
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()

def selected_rep(x,name):
 for tag,y in sr.representations(x):
  if tag==name:return y
 raise ValueError('Unknown exact representation')

def verify_conditional(aux,proposal,centers):
 if not isinstance(proposal,dict)or set(proposal)!={'rule','semantic','representation','branches','centers_sha256'}:raise ValueError('Malformed alpha proposal')
 if proposal['rule']!=RULE or proposal['semantic']!='ALPHA_SAFE':raise ValueError('Wrong terminal semantics; gamma is not proved')
 if proposal['centers_sha256']!=digest([[str(v)for v in c]for c in centers]):raise ValueError('Changed centers')
 x=sr.image(aux);y=selected_rep(x,proposal['representation']);brs=sorted_branches(y)
 if not isinstance(proposal['branches'],list)or len(proposal['branches'])!=len(brs):raise ValueError('Incomplete sorting coverage')
 results=[]
 for (name,z),entry in zip(brs,proposal['branches']):
  if set(entry)!={'branch','center'} or entry['branch']!=name or type(entry['center'])is not int or not 0<=entry['center']<4:raise ValueError('Invalid branch or center')
  j=entry['center'];target,ell,co=sorted_R(z)
  distance=max(max(abs(v.lo-a),abs(v.hi-a))for v,a in zip(target,centers[j][:22]))
  budget=distance+KAPPA[j]*ell.hi
  if budget>RADIUS:raise ValueError('Alpha height budget fails')
  results.append({'branch':name,'center':j,'distance':str(distance),'loss_upper':str(ell.hi),'budget':str(budget),'margin':str(RADIUS-budget)})
 return {'rule':RULE,'status':'ALPHA_SAFE','source_image_sha256':digest(aux),'representation':proposal['representation'],'branches':results,'does_not_prove_gamma_infeasibility':True}

def verify_bound_source(source,proposal,centers):
 if set(proposal)!={'source','port'}:raise ValueError('Malformed bound-source proposal')
 expected={n:source[n]for n in ('ordinal','index','path','parent_raw_sha256','projection_sha256','image_sha256')}
 if proposal['source']!=expected:raise ValueError('Wrong original source or path')
 if digest(source['aux_image'])!=source['image_sha256']:raise ValueError('Unbound reconstructed image')
 return verify_conditional(source['aux_image'],proposal['port'],centers)
