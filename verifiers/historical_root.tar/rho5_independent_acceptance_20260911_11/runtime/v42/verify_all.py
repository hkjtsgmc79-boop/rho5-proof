"""Read-only exact full component/certificate replay; absent root is not claimed."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent

def run(jobs):
 st=time.monotonic();manifest=json.loads((ROOT/'SHA256SUMS.json').read_text())
 for n,h in manifest.items():
  f=ROOT/n
  if not f.is_file()or hashlib.sha256(f.read_bytes()).hexdigest()!=h:raise ValueError('Wrong delivered file: '+n)
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1')
 outputs={}
 with tempfile.TemporaryDirectory(prefix='v42_full_replay_')as temp:
  for name,args in [
   ('verify_inputs',[]),('verify_algebra',[]),('verify_gain',[]),('verify_controls',[]),('verify_negative',[]),
   ('verify_dataset',['--jobs',str(jobs),'--output',str(Path(temp)/'full_dataset.json')])]:
   start=time.monotonic();r=subprocess.run([sys.executable,str(ROOT/(name+'.py'))]+args,env=env,cwd=ROOT,text=True,capture_output=True)
   if r.returncode:
    print(r.stdout);print(r.stderr,file=sys.stderr);raise RuntimeError(name+' failed')
   data=json.loads(r.stdout.strip().splitlines()[-1]);outputs[name]=data
   print(json.dumps({'component':name,'status':data['status'],'seconds':time.monotonic()-start}),flush=True)
 d=outputs['verify_dataset'];c=outputs['verify_controls'];g=outputs['verify_gain']
 result=dict(status='V42_ONE_SLACK_COMPENSATION_AND_THREE_PARENT_CERTIFICATES_PASS_NOT_GLOBAL_CLOSURE',
   received_open_frontiers=923,new_complete_parent_boxes=d['new_complete_count'],
   new_parent_indices=sorted(x['index']for x in d['new_complete_parents']),
   new_parent_coordinate_bounds=sum(x['added_bounds']for x in d['new_complete_parents']),
   structural_parent_hits=d['local_safe_parent_hits'],structural_cases=d['structural_cases'],
   provably_disjoint_tested_transport_families=d['disjoint_transport_families'],
   all923_k_obstruction=d['k_obstruction'],new_costs=[x['cost']for x in g['directions']],
   positive_width_new_domain=c['positive_width_new_outside_legacy_32_operations'],
   conditional_parent_results=d['conditional_parents'],
   negative_tests=outputs['verify_negative']['count'],symbolic_checks=outputs['verify_algebra']['identity_count'],
   unreceived_Round51_full_tree_replayed_here=False,whole_B_closed=False,macro_ledger='14/15',
   original_tree_modified=False,continuous_splits_added=0,manifest_files=len(manifest),seconds=time.monotonic()-st)
 return result
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--jobs',type=int,default=4);ap.add_argument('--output');a=ap.parse_args()
 if not 1<=a.jobs<=40:raise SystemExit('jobs must be 1..40')
 r=run(a.jobs)
 if a.output:Path(a.output).write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps(r),flush=True)
