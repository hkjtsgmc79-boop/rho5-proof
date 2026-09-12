"""Full exact replay of every supplied original-parent certificate and open cover.
No optimizer is imported by this entry point. Historical, unreceived trees are not replayed.
"""
from pathlib import Path
import argparse,hashlib,json,time,os,multiprocessing
from concurrent.futures import ProcessPoolExecutor,as_completed
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
ROOT=Path(__file__).resolve().parent

def check_file(path,expected):
 actual=hashlib.sha256(path.read_bytes()).hexdigest()
 if actual!=expected:raise ValueError('Hash mismatch: '+str(path))

def replay(item):
 from branch_protocol import verify
 p=json.loads((ROOT/item['parent_file']).read_text());c=json.loads((ROOT/item['certificate_file']).read_text())
 start=time.monotonic();r=verify(p,c,allow_open=not item['complete'],cross_check=True)
 if (r['status'] in ('EMPTY','SAFE')) != item['complete']:raise ValueError('Wrong declared completion for '+str(p['index']))
 if any(r['counts'].get(k,0)!=item['counts'].get(k,0) for k in set(r['counts'])|set(item['counts'])):raise ValueError('Stored counts disagree with exact replay')
 r['replay_seconds']=time.monotonic()-start
 return r

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--jobs',type=int,default=4);a=ap.parse_args()
 if not 1<=a.jobs<=40:raise ValueError('Use 1..40 jobs')
 t=time.monotonic()
 hashes=json.loads((ROOT/'MANIFEST_SHA256.json').read_text())
 for name,digest in hashes.items():check_file(ROOT/name,digest)
 received=json.loads((ROOT/'inputs/R52_SOURCE_MANIFEST.json').read_text())['files']
 frozen=0
 for f in (ROOT/'frozen/v41').rglob('*'):
  if not f.is_file() or '__pycache__' in f.parts:continue
  original='v41/'+str(f.relative_to(ROOT/'frozen/v41'))
  if original not in received:raise ValueError('Frozen file absent from received R52 manifest: '+original)
  check_file(f,received[original]);frozen+=1
 table=json.loads((ROOT/'INSERTION_INDEX.json').read_text())
 samples=json.loads((ROOT/'inputs/SAMPLE_INDEX.json').read_text())
 expected={r['index']:r for r in samples};ids=[r['index']for r in table['parents']]
 if len(ids)!=len(set(ids)) or set(ids)!=set(expected):raise ValueError('Duplicate or omitted supplied parent')
 for item in table['parents']:
  p=json.loads((ROOT/item['parent_file']).read_text());src=expected[item['index']]
  for k in ('index','sample','path','box','box_sha256'):
   if p[k]!=src[k] or item[k]!=src[k]:raise ValueError('Source parent identity mismatch: '+k)
  check_file(ROOT/item['parent_file'],item['parent_file_sha256'])
  check_file(ROOT/item['certificate_file'],item['certificate_file_sha256'])
 results=[]
 with ProcessPoolExecutor(max_workers=a.jobs,mp_context=multiprocessing.get_context('spawn'))as ex:
  for f in as_completed([ex.submit(replay,i)for i in table['parents']]):
   r=f.result();results.append(r)
   print(json.dumps({'parent_index':r['index'],'status':r['status'],'counts':r['counts'],'seconds':r['replay_seconds']},ensure_ascii=False),flush=True)
 from negative_tests import run as negative_tests
 negatives=negative_tests()
 completed=sorted([r for r in results if r['status']in('EMPTY','SAFE')],key=lambda r:r['index'])
 unpaid=sorted(r['index']for r in results if r['status']=='OPEN')
 def sumcounts(rows):
  keys=('nodes','S','C','I','H','A','O','new_waves','new_bounds')
  out={k:sum(r['counts'].get(k,0)for r in rows)for k in keys}
  out['maxdepth']=max(r['counts'].get('maxdepth',0)for r in rows)if rows else 0
  return out
 result={'status':'V44_COMPLETE_PARENT_CERTIFICATES_AND_PARTIAL_COVERS_PASSED_NOT_GLOBAL_CLOSURE','baseline_original_unpaid':754,
 'complete_parent_boxes':len(completed),'complete_parent_indices':[r['index']for r in completed],
 'remaining_selected_parent_boxes':len(unpaid),'unpaid_selected_parent_indices':unpaid,
 'proposed_original_unpaid_after_controller_graft':754-len(completed),'counts_complete_parents':sumcounts(completed),'counts_all_supplied_parents':sumcounts(results),
 'inherited_prefix_waves_complete':sum(r['prior_waves']for r in completed),'inherited_prefix_bounds_complete':sum(r['prior_bounds']for r in completed),
 'old_global_tree_replayed_here':False,'original_tree_modified':False,'controller_graft_and_deduplication_pending':True,
 'whole_B_closed':False,'macro_ledger':'14/15','all_closed_leaves_dense_cross_checked':True,'frozen_files_compared_to_R52':frozen,
 'static_files_checked':len(hashes),'negative_tests':negatives,'seconds':time.monotonic()-t}
 if result['complete_parent_boxes']!=table['complete_parent_boxes']:raise ValueError('Aggregate mismatch')
 print(json.dumps(result,ensure_ascii=False,sort_keys=True),flush=True)
if __name__=='__main__':main()
