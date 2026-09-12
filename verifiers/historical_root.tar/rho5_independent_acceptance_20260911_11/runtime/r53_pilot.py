from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
from concurrent.futures import ProcessPoolExecutor,as_completed
import argparse,hashlib,json,multiprocessing,os,time
for n in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[n]='1'
import r53_port as port
import bound_protocol as bp
ROOT=Path(__file__).resolve().parent

def read(p):return json.loads(p.read_text())
def write(p,r):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(r,indent=2)+'\n')
def worker(payload):
 src,outdir=payload
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 started=time.monotonic();prefix=src['partial_certificate'];ep=bp.endpoint(src['box'],prefix,True);assert ep['status']=='OPEN'
 aux=ep['aux_image'];result=port.check(aux)
 rec={'index':src['index'],'path':src['path'],'box':src['box'],'prefix':prefix,'endpoint':ep,'port':result,'seconds':time.monotonic()-started,'original_root_sha256':'4b72152fec20a58eff52ab6e93a8fd082fc85a28722d762412c0c5fc17abc707'}
 write(Path(outdir)/f"result_{src['index']:07d}.json",rec)
 return {'index':src['index'],'status':result['status'],'prefix_waves':ep['waves'],'prefix_bounds':ep['bounds'],'best_score_upper':result['best_score_upper'],'qualified_D_branches':result['qualified_D_branches'],'D_branches':result['D_branches'],'all_evaluated_targets_provably_disjoint':result['all_evaluated_targets_provably_disjoint'],'seconds':rec['seconds']}
if __name__=='__main__':
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,default=ROOT/'pilot16');parser.add_argument('--receipt',type=Path,default=ROOT/'receipts/V43_REPLAY.json');args=parser.parse_args()
 started=time.monotonic();args.out.mkdir();done=[]
 with ProcessPoolExecutor(max_workers=16,mp_context=multiprocessing.get_context('spawn'))as pool:
  for f in as_completed([pool.submit(worker,(s,str(args.out)))for s in read(ROOT/'PILOT16.json')]):done.append(f.result());print(json.dumps(done[-1]),flush=True)
 # Four meet endpoints were freshly recomputed by the immutable V43 default replay in this run.
 replay=read(args.receipt);assert replay['status']=='V43_P0_BOUNDARY_AND_R52_DIAGNOSTICS_PASS_NOT_GLOBAL_CLOSURE'
 graphs=[]
 for rec in replay['R52_diagnostic']['records']:
  for child in rec['children']:
   assert child['meet_status']=='BOUNDED'and child['meet_equals_old']
   ans=port.check(child['meet_endpoint']);graphs.append({'index':rec['index'],'label':child['label'],'port':ans,'origin':'Fresh V43 replay: both full same-source trajectories independently accepted before intersection; not an unverified cache.'})
 write(args.out/'FOUR_CONDITIONAL_PORTS.json',graphs)
 result={'status':'R53_SAME_SOURCE_PORT_PILOT_COMPLETE','parents':sorted(done,key=lambda r:r['index']),'outcomes':dict(Counter(r['status']for r in done)),'conditional_outcomes':dict(Counter(r['port']['status']for r in graphs)),'wall_seconds':time.monotonic()-started,'new_parent_certificates':0,'baseline_open':754,'original_tree_modified':False}
 write(args.out/'RESULT.json',result);print(json.dumps(result,indent=2))
