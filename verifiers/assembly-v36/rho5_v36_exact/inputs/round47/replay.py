from pathlib import Path
import json,hashlib,gzip,sys
ROOT=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
m=json.loads((ROOT/'MANIFEST.json').read_text())
assert set(m['models'])=={'I_LOW_ALPHA','II_LOW_ALPHA'}
for n,h in m['files'].items():assert sha(ROOT/n)==h,n
sys.path.insert(0,str(ROOT/'source'))
from verify_task import verify_task
out={}
for name,old in m['models'].items():
 tree=ROOT/old['tree_file'];assert sha(tree)==old['gzip_tree_sha256']
 h=hashlib.sha256()
 with gzip.open(tree,'rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 assert h.hexdigest()==old['raw_tree_sha256']
 result=verify_task(ROOT/'source/models'/name,tree,allow_open=not m['complete'])
 assert result['model_sha256']==old['model_sha256']
 for k in m['counters']:assert result.get(k,0)==old[k],(name,k)
 out[name]=result
assert all(v['open']==0 for v in out.values())==m['complete']
answer={'status':'V35_BOTH_LOW_ROOTS_ALPHA_COVERED' if m['complete'] else 'V35_EXTENDED_LOW_ROOTS_VALID_PARTIAL',
        'models':out,'independent_fresh_compile_and_complete_tree_replay':True,
        'macro_ledger':'11/15','whole_R_not_automatically_booked':True}
print(json.dumps(answer,indent=2))
