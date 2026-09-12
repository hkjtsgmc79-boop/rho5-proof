#!/usr/bin/env python3
"""Default V35 acceptance: local alpha theorems and supplied PARTIAL original roots.
This does not discover a tree and does not replay absent high-r archives.
"""
from pathlib import Path
import json,hashlib,tempfile,shutil,subprocess,time
ROOT=Path(__file__).resolve().parent

def main():
 start=time.monotonic();manifest=json.loads((ROOT/'MANIFEST.json').read_text())
 for name,want in manifest['files'].items():
  f=ROOT/name
  if not f.is_file()or hashlib.sha256(f.read_bytes()).hexdigest()!=want:raise ValueError('static file hash mismatch: '+name)
 from review_high_handoff import review
 from verify_local_certificate import verify
 from verify_v35_components import symbolic,check_controls,negative_certificate_tests
 from verify_checkpoint_protocol import verify as protocol
 from build_models import make_model,headers
 from verify_alpha_ports import test as test_ports
 high=review();local=verify(json.loads((ROOT/'local_wall_certificate.json').read_text()))
 symbols=symbolic();controls=check_controls();bad=negative_certificate_tests();checkpoint=protocol();results={}
 with tempfile.TemporaryDirectory(prefix='v35_full_cold_')as td:
  temp=Path(td);dirs={}
  for n in ('I_LOW_ALPHA','II_LOW_ALPHA'):
   md=ROOT/'models'/n;data=json.loads((md/'model.json').read_text());expected=make_model(data['K'],data['J'],data['type'],data['branch'])
   if data!=expected:raise ValueError('semantic model mismatch '+n)
   b=temp/n;b.mkdir();headers(data,b)
   for f in ('mc_exact_kernel.hpp','weighted_height.hpp','rankone_oracle.hpp','factor_graph.hpp','factor_oracle.hpp','mc_verify.cpp'):shutil.copy2(ROOT/'source'/f,b/f)
   cc=subprocess.run(['g++','-O3','-std=c++17','mc_verify.cpp','-o','verify'],cwd=b,text=True,capture_output=True,timeout=90)
   if cc.returncode:raise RuntimeError(cc.stderr)
   cp=subprocess.run([str(b/'verify'),str(md/'checkpoint.tree'),'--allow-open'],text=True,capture_output=True,timeout=60)
   if cp.returncode:raise RuntimeError(cp.stderr)
   results[n]=json.loads(cp.stdout);results[n]['model_sha256']=hashlib.sha256((md/'model.json').read_bytes()).hexdigest();results[n]['tree_sha256']=hashlib.sha256((md/'checkpoint.tree').read_bytes()).hexdigest();dirs[n]=b
   frozen=json.loads((ROOT/'evidence/PARTIAL_ORIGINAL_ROOTS.json').read_text())['models'][n]
   for key in ('nodes','splits','leaves','contradiction_leaves','alpha_safe_leaves','open','max_depth'):assert frozen[key]==results[n][key],(n,key)
  pp=temp/'port-tests';pp.mkdir();ports=test_ports(ROOT/'models/II_LOW_ALPHA',dirs['II_LOW_ALPHA']/'verify',pp)
 result={'status':'V35_LOCAL_ALPHA_FLOWS_AND_PARTIAL_ROOTS_PASS_NOT_GLOBAL_CLOSURE','static_files_hashed':len(manifest['files']),'high_handoff_review':high,'local_flow_certificate':local,'symbolic_dictionary_checks':symbols,'full_physical_controls':controls,'negative_local_tests':bad,'alpha_exit_tests':ports,'checkpoint_protocol':checkpoint,'original_roots':results,'nodes':sum(v['nodes']for v in results.values()),'contradiction_leaves':sum(v['contradiction_leaves']for v in results.values()),'alpha_safe_leaves':sum(v['alpha_safe_leaves']for v in results.values()),'open_frontiers':sum(v['open']for v in results.values()),'unreceived_high_trees_replayed_here':False,'whole_R':'OPEN','macro_B22':'OPEN','macro_ledger':'11/15','seconds':time.monotonic()-start}
 print(json.dumps(result,ensure_ascii=False))
if __name__=='__main__':main()
