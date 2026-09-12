from pathlib import Path
import gzip, hashlib, json
from verify_task import verify_task
ROOT=Path(__file__).resolve().parent
manifest=json.loads((ROOT/'MANIFEST.json').read_text())
for name,pin in manifest['files'].items():
 h=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
 if h!=pin:raise ValueError('File hash mismatch: '+name)
results={}
for name,pin in manifest['models'].items():
 tree=ROOT/'models'/name/'checkpoint.tree.gz'
 h=hashlib.sha256()
 with gzip.open(tree,'rb') as stream:
  for chunk in iter(lambda:stream.read(1048576),b''):h.update(chunk)
 if h.hexdigest()!=pin['tree_sha256']:raise ValueError('Tree hash mismatch: '+name)
 result=verify_task(ROOT/'models'/name,tree,allow_open=not manifest['both_complete'])
 for key in ('nodes','leaves','open','max_depth','model_sha256'):
  if result[key]!=pin[key]:raise ValueError('Replay counter/model mismatch: '+name+' '+key)
 results[name]=result
print(json.dumps({'status':'BOTH_ORIGINAL_ROOTS_COLD_PASS' if manifest['both_complete'] else 'PARTIAL_ORIGINAL_ROOTS_COLD_PASS_NO_NEW_FULL_RANGE', 'models':results},indent=2))
