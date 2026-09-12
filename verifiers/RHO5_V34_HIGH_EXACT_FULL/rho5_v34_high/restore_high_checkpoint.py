from pathlib import Path
import gzip,hashlib,json,shutil
ROOT=Path(__file__).resolve().parent
m=json.loads((ROOT/'MANIFEST.json').read_text())
assert set(m['models'])=={'I200_210_high','II200_210_high'}
out=ROOT/'resumed_high';out.mkdir()
records={}
for name,info in m['models'].items():
 tree=out/(name+'.tree')
 with gzip.open(ROOT/'results'/name/'checkpoint.tree.gz','rb') as f,tree.open('wb') as g:shutil.copyfileobj(f,g)
 h=hashlib.sha256()
 with tree.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 assert h.hexdigest()==info['tree_sha256']
 records[name]={**info,'tree':str(tree)}
(out/'CURRENT_STATE.json').write_text(json.dumps({'models':records,'status':'RESTORED_FROZEN_ORIGINAL_HIGH_ROOTS','ledger':'11/15'},indent=2)+'\n')
print('Restored without launching computation. Resume only these two models via fixed_source/run_campaign.py --output '+str(out))
