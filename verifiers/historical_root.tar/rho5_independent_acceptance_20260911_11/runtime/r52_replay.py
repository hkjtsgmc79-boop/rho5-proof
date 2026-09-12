"""Actual original-root traversal, with unchanged Round51 and versioned V42 terminals."""
from pathlib import Path
from collections import Counter
from concurrent.futures import ProcessPoolExecutor,wait,FIRST_COMPLETED
import argparse,hashlib,json,multiprocessing,os,time
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[key]='1'
import r51_replay as prior
from r52_protocol import structure,binding,new_result,tp
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check_chunk(payload):
 backend,items=payload;old_items=[v for v in items if v[1]['kind']not in ('B42','C42')]
 counts=Counter(prior.check_chunk((backend,old_items)))
 for box,node in items:
  kind=node['kind']
  if kind not in ('B42','C42'):continue
  val=new_result(box,node,backend);status={'EMPTY_HIGH':'EMPTY','SAFE_ALPHA':'SAFE'}[val['status']]
  counts[status]+=1;counts['checked']+=1;counts['kind:'+kind]+=1;counts['enclosure:V42_'+kind]+=1
  counts[kind+'_prefix_waves']+=val['prefix_waves'];counts[kind+'_prefix_bounds']+=val['prefix_bounds']
  cb=val.get('conditional_bounds',0);counts[kind+'_conditional_waves']+=val.get('conditional_waves',0);counts[kind+'_conditional_bounds']+=cb
  counts[kind+'_bounds']+=val['prefix_bounds']+cb
  if kind=='C42':
   assert sum(val['children'].values())==189 and val['children']['OPEN']==0
   counts['C42_checked_graphs']+=189
  if backend=='fraction':counts[kind+'_dense_crosschecks']+=val['prefix_bounds']+cb
 return dict(counts)
def replay(tree,workers,backend,allow_open):
 start=time.monotonic();tree=Path(tree);tree_hash=sha(tree)
 manifest=json.loads((ROOT/'R52_SOURCE_MANIFEST.json').read_text())
 for n,h in manifest['files'].items():assert sha(ROOT/n)==h,n
 tp.verify_partition();data=json.loads(tree.read_text());box=structure(data)
 stack=[(box,0)];counts=Counter();maximum=0;terminals=Counter();batch=[];futures=set()
 def collect(done):
  for future in done:terminals.update(future.result())
 with ProcessPoolExecutor(max_workers=workers,mp_context=multiprocessing.get_context('spawn'))as pool:
  for node in data['nodes']:
   if not stack:raise ValueError('unvisited records')
   box,depth=stack.pop();maximum=max(maximum,depth);counts[node['kind']]+=1
   if node['kind']=='S':
    left,right=tp.halve(box,node['axis']);stack.extend([(right,depth+1),(left,depth+1)])
   elif node['kind']=='O':pass
   else:batch.append((box,node))
   if len(batch)>=(1 if node['kind']in('W40','U41','G41','B42','C42')else 128):
    futures.add(pool.submit(check_chunk,(backend,batch)));batch=[]
    if len(futures)>=2*workers:
     done,futures=wait(futures,return_when=FIRST_COMPLETED);collect(done)
  if batch:futures.add(pool.submit(check_chunk,(backend,batch)))
  while futures:
   done,futures=wait(futures,return_when=FIRST_COMPLETED);collect(done)
 if stack:raise ValueError('truncated tree')
 assert terminals['checked']==sum(v for k,v in counts.items()if k not in ('S','O'))
 assert len(data['nodes'])==2*counts['S']+1
 assert terminals['EMPTY']+terminals['SAFE']+counts['O']==counts['S']+1
 assert sha(tree)==tree_hash
 if counts['O']and not allow_open:raise ValueError(f"{counts['O']} unpaid frontiers")
 return {'status':'COMPLETE_ALPHA_COVERAGE'if not counts['O']else'PARTIAL_EXACT_COVERAGE_ONLY',
  'nodes':len(data['nodes']),'splits':counts['S'],'contradictions':terminals['EMPTY'],'alpha_safe':terminals['SAFE'],
  'open':counts['O'],'max_depth':maximum,'kinds':dict(counts),'terminal_audit':dict(terminals),
  'whole_B_closed':not counts['O'],'macro_ledger':'14/15','controller_only_may_book_completion':True,
  'tree_sha256':tree_hash,'model_sha256':data['model_sha256'],'source_manifest_sha256':sha(ROOT/'R52_SOURCE_MANIFEST.json'),
  'r52_binding':binding(),'backend':backend,'workers':workers,'seconds':time.monotonic()-start,
  'scope':'Actual original B17 root; all original siblings and exact split boxes retained; every E/C/H/V/G/U40/W40/U41/G41/B42/C42 terminal checked',
  'new_leaf_backend':'Frozen Fraction references; backend=fraction adds dense residual checks for every U41 and B42/C42 prefix/conditional bound. Shared mathematics, not independent formalizations.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--tree',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--workers',type=int,default=40);p.add_argument('--backend',choices=('native','fraction'),default='native');p.add_argument('--allow-open',action='store_true');a=p.parse_args()
 if not 1<=a.workers<=40:raise ValueError('40-worker cap')
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 if a.out.exists():raise ValueError('immutable receipt exists')
 r=replay(a.tree,a.workers,a.backend,a.allow_open);a.out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
