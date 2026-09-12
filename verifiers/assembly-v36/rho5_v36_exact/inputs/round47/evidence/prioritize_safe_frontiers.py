#!/usr/bin/env python3
"""Prioritize existing alpha-ready boxes; leave all proof rules and roots intact."""
from pathlib import Path
import json,hashlib,fcntl
own=Path('/root/microscope_ws/rho5_cqg_v35_low_alpha_20260908/attempt_01')
root=own/'working_flow_tube'
lock=(root/'.campaign.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
p=root/'discovery/frontier_parallel.py';before=p.read_text()
old="    fronts.sort(key=lambda e:(len(e['steps']),e['model'],key(e['steps'])))"
new='''    # Scheduling only: all candidates still pass the unchanged C++ alpha
    # classifier and exact tree verifier. Every frontier keeps its owner.
    cert=json.loads((work/'local_wall_certificate.json').read_text())
    alpha=json.loads((work/'alpha.json').read_text());al=Fraction(alpha['isolating_interval']['lower'])
    scale=10**9;radius=Fraction(cert['outer_radius'])*scale;speed=Fraction(cert['uniform_speed_cap'])
    assert radius.denominator==1 and speed.denominator==1
    centers=[]
    for case in cert['cases']:
        c=[Fraction(v)*scale for v in case['center']];assert all(v.denominator==1 for v in c)
        centers.append([int(v) for v in c])
    def alpha_ready(e):
        lo,hi=e['lo'],e['hi'];unit=data[e['model']]['root_denominator']*(2**128)
        if 2*hi[1]*al.denominator<=al.numerator*unit:return True
        if (hi[1]-lo[2])*al.denominator<=al.numerator*unit:return True
        remaining=int(radius)*unit-int(speed)*scale*max(0,hi[1]+hi[2])
        if remaining<=0:return False
        return any(all(max(abs(lo[i]*scale-c[i]*unit),abs(hi[i]*scale-c[i]*unit))<remaining
                       for i in range(22)) for c in centers)
    for e in fronts:e['alpha_priority']=alpha_ready(e)
    fronts.sort(key=lambda e:(not e['alpha_priority'],len(e['steps']),e['model'],key(e['steps'])))'''
assert before.count(old)==1
(own/'frontier_parallel_before_priority.py').write_text(before)
p.write_text(before.replace(old,new))
compile(p.read_text(),str(p),'exec')
manifest=json.loads((root/'MANIFEST.json').read_text())
old_manifest=root/'reference/FLOW_TUBE_PRE_PRIORITY_MANIFEST.json'
old_manifest.write_text(json.dumps(manifest,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest['files']['reference/FLOW_TUBE_PRE_PRIORITY_MANIFEST.json']=sha(old_manifest)
manifest['files']['discovery/frontier_parallel.py']=sha(p)
(root/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
receipt={'status':'SCHEDULING_ONLY_ALPHA_READY_FRONTIERS_FIRST','all_frontiers_preserved':True,
         'exact_acceptor_changed':False,'model_root_or_rows_changed':False,
         'before_sha256':hashlib.sha256(before.encode()).hexdigest(),'after_sha256':sha(p)}
(own/'PRIORITY_SCHEDULING_CHANGE.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
