from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files={}
for manifest_name,prefix,key in [('HIGH_VALUE_SOURCE_MANIFEST.json','','files'),('v39/MANIFEST.json','v39/','sha256')]:
    m=json.loads((ROOT/manifest_name).read_text())
    for name,digest in m[key].items():
        path=ROOT/(prefix+name);assert sha(path)==digest,str(path);files[prefix+name]=digest
    files[manifest_name]=sha(ROOT/manifest_name)
for name in ('r49_protocol.py','r49_discovery.py','r49_graft.py','r49_apply.py','r49_replay.py','freeze_r49.py'):
    files[name]=sha(ROOT/name)
from r49_protocol import binding
result={'schema':'ROUND49_V39_ACCEPTING_SOURCE_V1','files':files,'binding':binding(),'whole_B_closed':False,'macro_ledger':'14/15'}
(ROOT/'R49_SOURCE_MANIFEST.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'R49_SOURCE_FROZEN','files':len(files),'manifest_sha256':sha(ROOT/'R49_SOURCE_MANIFEST.json'),'binding':binding()},indent=2))
