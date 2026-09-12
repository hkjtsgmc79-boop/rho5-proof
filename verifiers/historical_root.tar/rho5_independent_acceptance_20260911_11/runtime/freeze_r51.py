from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files={}
for manifest,prefix in [('R50_SOURCE_MANIFEST.json',''),('v41/MANIFEST.json','v41/')]:
 for name,digest in json.loads((ROOT/manifest).read_text())['files'].items():
  assert sha(ROOT/(prefix+name))==digest,name;files[prefix+name]=digest
 files[manifest]=sha(ROOT/manifest)
for name in ('r51_protocol.py','r51_scan.py','r51_apply.py','r51_replay.py','freeze_r51.py','test_r51.py'):files[name]=sha(ROOT/name)
from r51_protocol import binding
result={'schema':'ROUND51_FROZEN_ACCEPTING_SOURCE_V1','files':files,'binding':binding()}
(ROOT/'R51_SOURCE_MANIFEST.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'ROUND51_ACCEPTING_SOURCE_FROZEN','files':len(files),'sha256':sha(ROOT/'R51_SOURCE_MANIFEST.json'),'binding':binding()},indent=2))
