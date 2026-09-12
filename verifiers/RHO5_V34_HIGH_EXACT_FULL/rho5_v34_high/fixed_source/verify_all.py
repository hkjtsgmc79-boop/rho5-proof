#!/usr/bin/env python3
"""Verify V34 new mathematics and ALL saved original-root PARTIAL checkpoints.
This command is not a complete height proof unless the specified roots have no O.
The independent default acceptance of one mathematical task is verify_task.py,
which rejects every O leaf unless --allow-open was explicitly supplied.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile,shutil,time,argparse
ROOT=Path(__file__).resolve().parent

def digest(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()

def hashes(root):
 count=0
 for line in (root/'SHA256SUMS.txt').read_text().splitlines():
  sha,name=line.split('  ',1);p=root/name
  if not p.is_file()or digest(p)!=sha:raise ValueError('hash mismatch: '+name)
  count+=1
 return count

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--require-complete',action='store_true');a=ap.parse_args()
 start=time.monotonic();hcount=hashes(ROOT);records={}
 # All tests run on a temporary copy; shipped evidence is never overwritten.
 with tempfile.TemporaryDirectory(prefix='rho5_v34_cold_')as temp:
  run=Path(temp)/'rho5_v34_exact'
  def ignore_runtime(path,names):
   return [n for n in names if n in ('__pycache__','.campaign.lock','verify','discover_focus') or ((Path(path)/n).is_dir() and (n=='build' or n.startswith('build_') or n=='campaign'))]
  shutil.copytree(ROOT,run,ignore=ignore_runtime)
  sys.path.insert(0,str(run))
  from build_models import headers
  b=run/'build_test';b.mkdir(exist_ok=True)
  headers(json.loads((run/'models/I209_210_low/model.json').read_text()),b)
  for name in ('factor_probe.cpp','mc_exact_kernel.hpp','rankone_oracle.hpp','factor_graph.hpp','factor_oracle.hpp'):
   shutil.copy2(run/'source'/name,b/name)
  cp=subprocess.run(['g++','-O2','-std=c++17','factor_probe.cpp','-o','factor_probe'],cwd=b,capture_output=True,text=True)
  if cp.returncode:raise RuntimeError(cp.stderr)
  tests=['test_factor','test_cpp_packets','test_identities','test_light_input',
         'test_physical_oracle','test_physical_cycle_certificates','test_tree_protocol']
  for name in tests:
   p=subprocess.run([sys.executable,str(run/'tests'/(name+'.py'))],cwd=run,capture_output=True,text=True)
   if p.returncode:raise RuntimeError(name+'\n'+p.stdout+'\n'+p.stderr)
   print(p.stdout.strip(),flush=True);records[name]=json.loads(p.stdout.strip().splitlines()[-1])
  checkpoints={}
  for model in sorted((run/'models').iterdir()):
   if not (model/'model.json').exists():continue
   p=subprocess.run([sys.executable,str(run/'verify_task.py'),str(model),'--allow-open'],cwd=run,capture_output=True,text=True)
   if p.returncode:raise RuntimeError(model.name+'\n'+p.stdout+'\n'+p.stderr)
   result=json.loads(p.stdout);saved=json.loads((model/'PILOT_ACCEPTANCE.json').read_text())
   for key in ('nodes','splits','leaves','open','max_depth','full_factor_leaves','factor_graph_leaves','factor_direct_leaves','model_sha256'):
    if result[key]!=saved[key]:raise ValueError(model.name+' saved counters/binding mismatch '+key)
   checkpoints[model.name]=result
   print(json.dumps({'event':'original_root_checkpoint_replayed','model':model.name,**result}),flush=True)
 totalopen=sum(x['open'] for x in checkpoints.values())
 result={'status':'V34_COMPONENTS_AND_PARTIAL_ROOTS_PASS_NOT_GLOBAL_CLOSURE' if totalopen else 'V34_COMPONENTS_AND_SELECTED_ROOTS_PASS',
         'hash_files':hcount,'tests':records,'models':checkpoints,'open_frontiers':totalopen,
         'nodes':sum(x['nodes']for x in checkpoints.values()),'closed_leaves':sum(x['leaves']for x in checkpoints.values()),
         'factor_graph_leaves':sum(x['factor_graph_leaves']for x in checkpoints.values()),
         'omitted_round45_trees_replayed_here':False,'whole_R':'OPEN','macro_B22':'OPEN','macro_ledger':'11/15',
         'seconds':time.monotonic()-start}
 print(json.dumps(result),flush=True)
 if a.require_complete and totalopen:raise SystemExit(2)
if __name__=='__main__':main()
