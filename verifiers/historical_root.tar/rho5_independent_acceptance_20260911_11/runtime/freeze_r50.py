from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files={}
for manifest,prefix in [('R49_SOURCE_MANIFEST.json',''),('v40/MANIFEST.json','v40/')]:
 for name,digest in json.loads((ROOT/manifest).read_text())['files'].items():
  assert sha(ROOT/(prefix+name))==digest,name
  files[prefix+name]=digest
 files[manifest]=sha(ROOT/manifest)
for name in ('r50_protocol.py','r50_scan.py','r50_apply.py','r50_replay.py','freeze_r50.py','test_r50.py','r50_unconditional.py','r50_uscan.py','test_r50_unconditional.py'):files[name]=sha(ROOT/name)
from r50_protocol import binding
result={'schema':'ROUND50_FROZEN_ACCEPTING_SOURCE_V1','files':files,'binding':binding()}
(ROOT/'R50_SOURCE_MANIFEST.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'R50_SOURCE_FROZEN','files':len(files),'sha256':sha(ROOT/'R50_SOURCE_MANIFEST.json'),'binding':binding()},indent=2))
