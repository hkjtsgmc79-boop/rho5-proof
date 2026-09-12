from pathlib import Path
import hashlib,json
from r52_protocol import binding
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files={}
for name,prefix in [('R51_SOURCE_MANIFEST.json',''),('v42/SHA256SUMS.json','v42/')]:
 m=json.loads((ROOT/name).read_text());m=m.get('files',m)
 for n,h in m.items():assert sha(ROOT/(prefix+n))==h,n;files[prefix+n]=h
 files[name]=sha(ROOT/name)
for n in ('r52_protocol.py','r52_replay.py','r52_apply.py','r52_condition_probe.py','r52_refined_parents.py','compare_and_expand.py','test_r52.py','freeze_r52.py'):files[n]=sha(ROOT/n)
r={'schema':'ROUND52_FROZEN_ACCEPTING_SOURCE_V1','files':files,'binding':binding()}
p=ROOT/'R52_SOURCE_MANIFEST.json';assert not p.exists();p.write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'status':'ROUND52_ACCEPTING_SOURCE_FROZEN','files':len(files),'sha256':sha(p),'binding':r['binding']},indent=2))
