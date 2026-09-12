"""Optional short-budget discovery with the unchanged V41 acceptance rule.
This does not alter a production tree. --additional-waves is not a closure promise.
"""
from pathlib import Path
import argparse,importlib.util,json,os,time
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
from _v42_bootstrap import prepare,v41_api,canonical_hash

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('source_record');ap.add_argument('--output',required=True)
 ap.add_argument('--additional-waves',type=int,default=4);ap.add_argument('--seconds',type=float,default=60)
 a=ap.parse_args()
 if not 0<=a.additional_waves<=32 or a.seconds<0:raise SystemExit('Finite nonnegative short budget required')
 s=json.loads(Path(a.source_record).read_text());box=s['box'];incoming=s['partial_certificate']
 vp,db,sa=v41_api();vp.verify(box,incoming,allow_open=True,cross_check=True)
 out=Path(a.output);out.parent.mkdir(parents=True,exist_ok=True)
 if out.exists():
  current=json.loads(out.read_text());vp.verify(box,current,allow_open=True,cross_check=True)
 else:current=incoming;out.write_text(json.dumps(current)+'\n')
 if current['trace']['profile']!=incoming['trace']['profile']:raise ValueError('No silent profile change')
 start=len(current['trace']['waves']);cap=min(128,start+a.additional_waves)
 spec=importlib.util.spec_from_file_location('v42_unchanged_discovery',prepare()['v41']/'discovery.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 t=time.monotonic();r=m.discover_parent(box,out,profile=current['trace']['profile'],max_waves=cap,seconds=a.seconds)
 result=json.loads(out.read_text());exact=vp.verify(box,result,allow_open=True,cross_check=True)
 receipt=dict(exact=exact,discovery=r,source_index=s.get('index'),source_path=s.get('path'),
  initial_reused_waves=start,total_wave_cap=cap,seconds=time.monotonic()-t,
  certificate_sha256=canonical_hash(result),original_tree_modified=False)
 out.with_suffix(out.suffix+'.task_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt))
