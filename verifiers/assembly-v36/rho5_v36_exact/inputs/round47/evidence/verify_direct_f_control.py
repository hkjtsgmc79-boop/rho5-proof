#!/usr/bin/env python3
"""Replay the new A6 on an exact physical source rejected by every old A exit."""
from pathlib import Path
from fractions import Fraction as Q
import argparse,sys,json,hashlib,subprocess

ap=argparse.ArgumentParser();ap.add_argument('--package',type=Path,required=True)
ap.add_argument('--probe',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
a=ap.parse_args();root=a.package.resolve();sys.path.insert(0,str(root));sys.path.insert(0,str(root/'discovery'))
from native import verify_matrix
from alpha_ports import proves
import frontier_parallel as fp
probe=json.loads(a.probe.read_text());records=[r for r in probe['records'] if not r['safe_codes']]
assert records,'Need a real control establishing the gap of the old exits'
rec=max(records,key=lambda r:Q(r['gamma_gap']))
ans=verify_matrix(rec['matrix']);z=ans['point'];z.append(z[8]*z[10])
md=root/'models/II_LOW_ALPHA';model=json.loads((md/'model.json').read_text())
assert model['parent_model_sha256']==probe['model_sha256']
assert ans['strict_first_three'] and str(ans['F'])==rec['F']
box=[(x,x) for x in z];assert not any(proves(box,c) for c in range(6))
assert proves(box,6)
unit=model['root_denominator']*2**128
lo,hi=[list(side) for side in fp.root_box(model)];steps=[]
assert all(Q(l,unit)<=v<=Q(h,unit) for l,v,h in zip(lo,z,hi))
while not proves([(Q(l,unit),Q(h,unit)) for l,h in zip(lo,hi)],6):
    j=max((1,2),key=lambda i:hi[i]-lo[i]);m=(lo[j]+hi[j])//2
    assert lo[j]<m<hi[j] and (lo[j]+hi[j])%2==0
    b=int(z[j]*unit>m);steps.append((j,b))
    if b:lo[j]=m
    else:hi[j]=m
    assert len(steps)<200
a.out.mkdir(parents=True,exist_ok=True)
tree=a.out/'EXACT_OUTSIDE_OLD_A_NOW_A6.tree';tree.write_bytes(fp.envelope(steps,b'A 6\n'))
result=fp.run_verify(md/'verify',tree)
assert result['alpha_safe_leaves']==1 and result['direct_height_leaves']==1
assert result['contradiction_leaves']==0 and result['open']==len(steps)
rejects=[]
for tag in ('A 6\n','A 7\n','A -1\n'):
    p=a.out/('BAD_'+tag.strip().replace(' ','_')+'.tree');p.write_text(tag)
    r=subprocess.run([str(md/'verify'),str(p),'--allow-open'],text=True,capture_output=True)
    assert r.returncode!=0;rejects.append(tag.strip())
r=subprocess.run([str(md/'verify'),str(tree)],text=True,capture_output=True)
assert r.returncode!=0;rejects.append('unpaid siblings in strict mode')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
out={'status':'EXACT_FULL_PHYSICAL_CONTROL_REQUIRES_NEW_EXIT_AND_A6_ACCEPTED',
     'alpha_counterexample':False,'control':rec,'tree':str(tree),'tree_sha256':sha(tree),
     'model_sha256':sha(md/'model.json'),'parent_model_sha256':model['parent_model_sha256'],
     'replay':result,'negative_cases_rejected':rejects,'whole_root_complete':False}
(a.out/'DIRECT_F_CONTROL_RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='control'},indent=2))
