#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((ROOT/'MANIFEST.json').read_text())
for name,digest in manifest['sha256'].items():assert sha(ROOT/name)==digest,name
files=dict(manifest['sha256']);files['MANIFEST.json']=sha(ROOT/'MANIFEST.json')
for name in ('b17_native.cpp','b17_native_data.hpp','generate_native_data.py','build_native.py','native_backend.py',
             'native_probe.py','native_campaign.py','test_native.py','test_native_transport.py','test_composition.py','freeze_native_source.py'):
    files[name]=sha(ROOT/name)
out={'schema':'ROUND48_B17_NATIVE_EXACT_SOURCE_V1','model_sha256':files['models/B17_FULL.json'],
     'parent_static_manifest_sha256':files['MANIFEST.json'],'files':files,'macro_ledger':'14/15',
     'scope':'Same B17 root and original E/C/H canonical enclosure semantics; C++ exact rational port and fair search; no P or B18 contacts',
     'whole_B_closed':False}
(ROOT/'NATIVE_SOURCE_MANIFEST.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'NATIVE_SOURCE_FROZEN','files':len(files),'manifest_sha256':sha(ROOT/'NATIVE_SOURCE_MANIFEST.json')},indent=2))
