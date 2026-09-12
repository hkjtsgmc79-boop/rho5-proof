#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
original=json.loads((ROOT/'MANIFEST.json').read_text())
for name,digest in original['sha256'].items():assert sha(ROOT/name)==digest,name
files=dict(original['sha256']);files['MANIFEST.json']=sha(ROOT/'MANIFEST.json')
for path in sorted(ROOT.iterdir()):
    if path.is_file()and path.suffix in ('.py','.cpp','.hpp','.md'):files[path.name]=sha(path)
files['HIGH_VALUE_RULE.json']=sha(ROOT/'HIGH_VALUE_RULE.json')
result={'schema':'ROUND48_B17_HIGH_VALUE_SOURCE_V1','files':files,'model_sha256':files['models/B17_FULL.json'],
        'parent_static_manifest_sha256':files['MANIFEST.json'],'enclosure':'high_value_v1',
        'scope':'Untagged original V37 leaves retain original semantics. Explicit high_value_v1 leaves use necessary-inequality contraction; unknown versions reject. Root, alpha, 106 rows and 38 products unchanged.',
        'native_build':'Regenerate frozen header and compile with build_native.py before native replay',
        'whole_B_closed':False,'macro_ledger':'14/15'}
(ROOT/'HIGH_VALUE_SOURCE_MANIFEST.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'HIGH_VALUE_SOURCE_FROZEN','files':len(files),'manifest_sha256':sha(ROOT/'HIGH_VALUE_SOURCE_MANIFEST.json')}))
