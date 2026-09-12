from pathlib import Path
import gzip,hashlib,json,sys
ROOT=Path(__file__).resolve().parent
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
m=json.loads((ROOT/'MANIFEST.json').read_text())
assert set(m['models'])=={'I200_210_high','II200_210_high'}
for name,pin in m['files'].items():assert digest(ROOT/name)==pin,name
sys.path.insert(0,str(ROOT/'fixed_source'))
from verify_task import verify_task
results={}
for name,old in m['models'].items():
 tree=ROOT/'results'/name/'checkpoint.tree.gz';h=hashlib.sha256()
 with gzip.open(tree,'rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 assert h.hexdigest()==old['tree_sha256']
 result=verify_task(ROOT/'fixed_source/models'/name,tree,allow_open=not m['complete'])
 for key in ('model_sha256','nodes','splits','leaves','open','max_depth','full_factor_leaves'):assert result[key]==old[key],key
 results[name]=result
assert all(v['open']==0 for v in results.values())==m['complete']
print(json.dumps({'status':'V34_BOTH_HIGH_ROOTS_PORTABLE_COLD_PASS' if m['complete'] else 'V34_PARTIAL_HIGH_ROOTS_PORTABLE_COLD_PASS_NO_CLOSURE','models':results,'r_equal_k':'low_branch_only','macro_ledger':'11/15'},indent=2))
