#!/usr/bin/env python3
"""Default: exact inputs, algebra, controls, ALL 64 conditional covers.
No LP solver. No unreceived original-root tree is silently replayed.
"""
import os
for n in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):os.environ[n]='1'
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,time,importlib.util,sys
ROOT=Path(__file__).resolve().parent

def local_verifier(name):
 # Frozen dependencies intentionally have their own verify_math/negative files.
 # Load THIS version by exact file path, never by altered sys.path precedence.
 path=ROOT/(name+'.py');module_name='_v40_local_'+name
 spec=importlib.util.spec_from_file_location(module_name,path)
 module=importlib.util.module_from_spec(spec);sys.modules[module_name]=module
 spec.loader.exec_module(module)
 assert Path(module.__file__).resolve()==path.resolve()
 return module

def check_static():
 manifest=ROOT/'MANIFEST.json'
 if not manifest.is_file():raise ValueError('Static manifest missing')
 data=json.loads(manifest.read_text())['files']
 for rel,expected in data.items():
  p=ROOT/rel
  if not p.is_file()or hashlib.sha256(p.read_bytes()).hexdigest()!=expected:raise ValueError('Static file mismatch: '+rel)
 return len(data)

def one(i):
 from protocol import verify_parent
 p=ROOT/'evidence/parents'/f'sample_{i:02d}.json';cert=json.loads(p.read_text())
 # Partial files must retain their unpaid alternatives. Default mathematical
 # success for one parent still requires no OPEN. This driver reports both.
 partial=any(r['mode']=='OPEN'for r in cert['children'].values())
 return verify_parent(cert['box'],cert,allow_open=partial)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--jobs',type=int,default=4);args=ap.parse_args()
 if args.jobs<1:raise ValueError('jobs must be positive')
 start=time.monotonic();static=check_static();print('STATIC_MANIFEST_PASS',static,flush=True)
 verify_input,verify_math,verify_negative,verify_ablation=[local_verifier(n)for n in ('verify_input','verify_math','verify_negative','verify_ablation')]
 inp=verify_input.run();print('INPUT_REVIEW_PASS',json.dumps(inp),flush=True)
 math=verify_math.run();assert math['all_source_homogenization_identity_checks']==3996;print('EXACT_MATH_CONTROLS_PASS',json.dumps(math),flush=True)
 neg=verify_negative.run();assert neg['rejection_controls']==27;print('NEGATIVE_CONTROLS_PASS',json.dumps(neg),flush=True)
 ablation=verify_ablation.run();print('ABLATION_CERTIFICATES_PASS',json.dumps(ablation),flush=True)
 if args.jobs==1:receipts=[one(i)for i in range(64)]
 else:
  with concurrent.futures.ProcessPoolExecutor(max_workers=args.jobs)as pool:receipts=list(pool.map(one,range(64)))
 complete=[r['sample_ordinal']for r in receipts if r['children']['OPEN']==0]
 opens=[r['sample_ordinal']for r in receipts if r['children']['OPEN']]
 counts={key:sum(r['children'][key]for r in receipts)for key in('EMPTY','SAFE','OPEN')}
 assert len(complete)==51 and len(opens)==13 and counts['OPEN']==70
 assert counts['EMPTY']+counts['SAFE']+counts['OPEN']==64*189
 assert all(r['status']=='COMPLETE_BOX_HIGH_EMPTY'for r in receipts if not r['children']['OPEN'])
 modes={};kinds={}
 for r in receipts:
  for key,v in r['modes'].items():modes[key]=modes.get(key,0)+v
  for key,v in r['kinds'].items():kinds[key]=kinds.get(key,0)+v
 insertion=json.loads((ROOT/'evidence/INSERTION_INDEX.json').read_text())
 for rr,index in zip(receipts,insertion):assert rr['reported_index']==index['reported_index']and rr['children']['OPEN']==index['open_graphs']
 result={'status':'V40_PROJECTIVE_COUPLING_AND_51_BOX_CERTIFICATES_PASS_NOT_GLOBAL_CLOSURE',
 'complete_parent_boxes':51,'remaining_sample_parent_boxes':13,'open_conditional_graphs':70,
 'subgraphs':counts,'modes':modes,'proof_kinds':kinds,'complete_sample_ordinals':complete,
 'remaining_sample_ordinals':opens,'static_files':static,'input_review':inp,'mathematics':math,'negative_tests':neg,'ablation':ablation,
 'full_parent_receipts':receipts,'unreceived_round49_full_tree_replayed_here':False,
 'actual_original_tree_ancestry_independently_verified_here':False,'whole_B_closed':False,
 'macro_ledger':'14/15','seconds':round(time.monotonic()-start,3)}
 print(json.dumps(result,separators=(',',':')),flush=True)
if __name__=='__main__':main()
