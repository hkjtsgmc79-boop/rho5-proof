from pathlib import Path
from fractions import Fraction as Q
import sys,json
R=Path(__file__).resolve().parent;sys.path.insert(0,str(R/'data/deep'));import deep_math as dm
bp=dm.load_protocol(R/'data/deep')
s=json.loads((R/'SOURCE_REBUILD.json').read_text())['records'][0]
w=json.loads((R/'WITNESS_MEMBERSHIP.json').read_text());point=[Q(w['B24'][n])for n in 'k r s t A B c d p e beta u0 u1 u2 x0 x1 x2 v0 v1 v2 q0 q1 q2 F'.split()]
parent=json.loads((R/'data'/s['parent_file']).read_text());cert=json.loads((R/'data'/s['projection_file']).read_text());o,old=bp.prefix_image(parent,cross_check=True);node=cert['tree'];cuts=[]
for dep in range(len(s['path'])+1):
 o=bp.db.common_contract(o,profile=cert['profile'])
 for wave in node['waves']:o=bp.db.apply_wave(o,wave,profile=cert['profile'],cross_check=True)
 if o['status']!='BOUNDED':raise ValueError('unexpected empty')
 for i,(lo,hi)in enumerate(o['aux_image']):
  if not Q(lo)<=point[i]<=Q(hi):raise ValueError('witness failed ancestor inclusion')
 if dep==len(s['path']):
  if node['terminal']!={'kind':'O'}:raise ValueError('wrong node')
  if bp.json_hash(o['aux_image'])!=s['image_sha256']:raise ValueError('image mismatch')
  break
 t=node['terminal'];ax=t['axis'];b=[list(v)for v in o['aux_image']];lo,hi=map(Q,b[ax]);mid=(lo+hi)/2;br=s['path'][dep]
 margin=mid-point[ax]if br=='0'else point[ax]-mid
 if margin<0:raise ValueError('wrong side of exact ancestor split')
 cuts.append({'depth':dep,'axis':ax,'branch':br,'midpoint':str(mid),'point_coordinate':str(point[ax]),'signed_margin':str(margin)})
 if br=='0':b[ax][1]=str(mid);node=t['left']
 else:b[ax][0]=str(mid);node=t['right']
 o={'status':'BOUNDED','aux_image':b}
out={'status':'ALL_24_EXACT_ANCESTOR_BRANCHES_CONTAIN_WITNESS','witness_sha256':dm.file_sha(R/'WITNESS_MEMBERSHIP.json'),'source_identity':s['projection_sha256'],'cuts':cuts,'all_ancestor_images_contain_witness':True,'all_cuts_strict':all(Q(z['signed_margin'])>0 for z in cuts)}
(R/'WITNESS_PATH_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'],out['all_cuts_strict'])
