#!/usr/bin/env python3
"""Review received high-r model/receipt interfaces; never replay omitted trees."""
from pathlib import Path
import tempfile,zipfile,json,hashlib,importlib.util,sys,subprocess
ROOT=Path(__file__).resolve().parent

def review():
 with tempfile.TemporaryDirectory(prefix='v35_input_review_') as tmp:
  H=Path(tmp)
  with zipfile.ZipFile(ROOT/'inputs/RHO5_V34_HIGH_FIX_RESULTS_LIGHT.zip') as a:
   for name in a.namelist():
    target=(H/name).resolve()
    if not target.is_relative_to(H):raise ValueError('unsafe archive member')
   a.extractall(H)
  manifest=json.loads((H/'LIGHT_MANIFEST.json').read_text());checked=[]
  for name,dig in manifest['files'].items():
   p=H/name;assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==dig,name;checked.append(name)
  inner_counts={}
  for m in [H/'compute_export/LIGHT_MANIFEST.json',H/'implementation_fix/LIGHT_MANIFEST.json']:
   d=json.loads(m.read_text());count=0
   for name,ent in d.get('files',{}).items():
    sha=ent if isinstance(ent,str)else ent.get('sha256')
    if sha:
     p=m.parent/name;assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==sha,str(p);count+=1
   inner_counts[str(m.relative_to(H))]=count
  spec=importlib.util.spec_from_file_location('v35_received_high_source',H/'compute_export/build_models.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
  rebuilt=[]
  for typ in ['I','II']:
   name=typ+'200_210_high';f=H/'compute_export/models'/name/'model.json';old=json.loads(f.read_text());new=module.make_model('2','21/10',typ,'high');assert old==new,name
   rebuilt.append({'name':name,'model_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'variables':len(new['variables']),'rows':len(new['rows']),'products':len(new['pairs'])})
  cp=subprocess.run([sys.executable,str(H/'evidence/verify_high_transpose.py'),str(H/'transpose_output')],text=True,capture_output=True,timeout=40);assert cp.returncode==0,cp.stderr;tr=json.loads(cp.stdout)
  local=json.loads((H/'compute_export/FRESH_LOCAL_REPLAY_RESULT.json').read_text());assert set(local['models'])=={'I200_210_high','II200_210_high'}
  for name,d in local['models'].items():
   assert d['open']==0 and d['nodes']==2*d['splits']+1 and d['leaves']==d['splits']+1
   for key in ('nodes','leaves','model_sha256'):assert d[key]==manifest['models'][name][key]
  fixed=H/'compute_export/source/factor_graph.hpp';h=hashlib.sha256(fixed.read_bytes()).hexdigest();assert h=='157c63d6d6b3c170241e36e7a28c4ab722cfc6bb97a41b791e99ec7ebced9379'
  assert (ROOT/'source/factor_graph.hpp').read_bytes()==fixed.read_bytes()
  return {'status':'V35_HIGH_HANDOFF_INTERFACE_REVIEW_PASS','top_level_files_hashed':len(checked),'inner_manifest_files':inner_counts,'semantic_models_rebuilt':rebuilt,'actual_transpose_zero_checks':tr['exact_zero_checks'],'actual_transpose_negative_controls':tr['negative_controls'],'local_record_nodes':sum(d['nodes']for d in local['models'].values()),'local_record_closed_leaves':sum(d['leaves']for d in local['models'].values()),'local_record_open':sum(d['open']for d in local['models'].values()),'fixed_factor_header_sha256':h,'unreceived_complete_trees_replayed_here':False,'ASAN_reexecuted_here':False,'residual_scope':'2<k<21/10, r<=k including equality; exact alpha','macro_ledger':'11/15'}
if __name__=='__main__':print(json.dumps(review(),indent=2))
