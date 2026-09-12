#!/usr/bin/env python3
"""Accept the six real stalled ancestor boxes using exact certified flow tubes."""
from pathlib import Path
from fractions import Fraction as Q
import argparse,json,gzip,sys,subprocess,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--package',type=Path,required=True)
ap.add_argument('--frontiers',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
a=ap.parse_args();root=a.package.resolve();sys.path.insert(0,str(root));sys.path.insert(0,str(root/'discovery'))
from alpha_ports import proves
from verify_local_certificate import verify
import frontier_parallel as fp
cert=json.loads((root/'local_wall_certificate.json').read_text());local=verify(cert)
md=root/'models/II_LOW_ALPHA';model=json.loads((md/'model.json').read_text());a.out.mkdir(parents=True,exist_ok=True)
records=[]
with gzip.open(a.frontiers,'rt') as stream:
 for line in stream:
  f=json.loads(line)
  if len(f['steps'])<500 or f['direct_F_safe']:continue
  unit=int(f['unit']);box=[(Q(int(l),unit),Q(int(h),unit)) for l,h in zip(f['lo'],f['hi'])]
  assert not any(proves(box,c) for c in range(7))
  codes=[c for c in range(7,11) if proves(box,c)];assert codes
  code=codes[0];tree=a.out/f'STALLED_BOX_{len(records):02d}_A{code}.tree'
  tree.write_bytes(fp.envelope(f['steps'],f'A {code}\n'.encode()))
  res=fp.run_verify(md/'verify',tree)
  assert res['alpha_safe_leaves']==1 and res['flow_tube_leaves']==1 and res['contradiction_leaves']==0
  assert res['open']==len(f['steps']) and res['max_depth']==500
  # Extracting the owned payload must retain the new terminal exactly.
  payload=a.out/(tree.stem+'_payload.tree')
  with payload.open('wb') as out:fp.copy_focused_payload(tree,f['steps'],out)
  assert payload.read_text()==f'A {code}\n'
  records.append({'code':code,'path':str(tree),'tree_sha256':fp.digest(tree),'acceptance':res,
                  'F_upper':str(box[1][1]-box[2][0]),'old_0_through_6_all_fail':True})
assert len(records)==6
# Cache must never accept a changed tree just because the filename is unchanged,
# or reuse an allow-open result as a strict success.
t=a.out/'CACHE_BINDING.tree';t.write_text('O\n');one=fp.run_verify(md/'verify',t)
two=fp.run_verify(md/'verify',t);assert one==two and one['open']==1
rejections=[]
try:fp.run_verify(md/'verify',t,False)
except RuntimeError:rejections.append('strict flag cannot reuse open receipt')
else:raise AssertionError('cache ignored strict mode')
for tag in ('A 9\n','A 11\n','A -1\n'):
 t.write_text(tag)
 try:fp.run_verify(md/'verify',t)
 except RuntimeError:rejections.append(tag.strip())
 else:raise AssertionError('cache reused different tree bytes')
result={'status':'CERTIFIED_FLOW_TUBES_PAY_ALL_SIX_STALLED_BOXES',
        'local_certificate':local,'boxes':records,'cache_negative_cases':rejections,
        'model_sha256':fp.digest(md/'model.json'),'rule_sha256':fp.digest(root/'DIRECT_F_RULE.json'),
        'whole_root_complete':False,'no_unpaid_siblings_removed':True}
(a.out/'FLOW_TUBE_STALLED_BOXES_RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('local_certificate','boxes')},indent=2))
