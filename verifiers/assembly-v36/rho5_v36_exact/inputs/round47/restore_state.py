from pathlib import Path
import json,hashlib,gzip,shutil
ROOT=Path(__file__).resolve().parent
m=json.loads((ROOT/'MANIFEST.json').read_text());models={}
for name,old in m['models'].items():
 archived=ROOT/old['tree_file'];h=hashlib.sha256(archived.read_bytes()).hexdigest()
 assert h==old['gzip_tree_sha256']
 tree=ROOT/'source/campaign_low_alpha/restored'/f'{name}.tree';tree.parent.mkdir(parents=True,exist_ok=True)
 with gzip.open(archived,'rb') as src,tree.open('wb') as out:shutil.copyfileobj(src,out)
 h=hashlib.sha256(tree.read_bytes()).hexdigest();assert h==old['raw_tree_sha256']
 models[name]={**{k:old[k] for k in m['counters']},'tree':str(tree),'tree_sha256':h,
               'model_sha256':old['model_sha256'],'raw_tree_sha256':old['raw_tree_sha256'],
               'original_root_accepted':True}
p=ROOT/'source/campaign_low_alpha/CURRENT_STATE.json';p.parent.mkdir(exist_ok=True)
p.write_text(json.dumps({'expected_models':list(models),'models':models,'workers_cap':40,'ledger':'11/15',
 'status':'COMPLETE_SELECTED_ORIGINAL_ROOTS' if m['complete'] else 'EXACT_PARTIAL_ORIGINAL_ROOTS'},indent=2)+'\n')
print(p)
