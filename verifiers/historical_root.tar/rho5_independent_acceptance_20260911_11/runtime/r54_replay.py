"""Every original terminal, including complete B44 subcovers, on its actual B17 ancestor box."""
from pathlib import Path
from collections import Counter
from concurrent.futures import ProcessPoolExecutor,wait,FIRST_COMPLETED
import argparse,hashlib,json,multiprocessing,os,time
for n in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[n]='1'
import r52_replay as prior
from r54_protocol import structure,binding,verify_b44,tp
ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check_chunk(payload):
 backend,items=payload
 counts=Counter(prior.check_chunk((backend,[(box,node)for box,node,idx,path in items if node['kind']!='B44'])))
 for box,node,idx,path in items:
  if node['kind']!='B44':continue
  v=verify_b44(box,idx,path,node);c=v['counts'];counts[v['status']]+=1;counts['checked']+=1;counts['kind:B44']+=1;counts['enclosure:V44_B44']+=1
  counts['B44_prefix_waves']+=v['prior_waves'];counts['B44_prefix_bounds']+=v['prior_bounds']
  for k in ('nodes','S','C','I','H','A','O','new_waves','new_bounds'):counts['B44_local_'+k]+=c.get(k,0)
  counts['B44_always_dense_bound_checks']+=v['prior_bounds']+c.get('new_bounds',0)
  counts['B44_always_dense_terminal_checks']+=c.get('C',0)+c.get('H',0)
 return dict(counts)
def replay(tree,workers,backend,allow_open):
 start=time.monotonic();tree=Path(tree);tree_sha=sha(tree)
 for n,h in json.loads((ROOT/'R54_SOURCE_MANIFEST.json').read_text())['files'].items():assert sha(ROOT/n)==h,n
 tp.verify_partition();data=json.loads(tree.read_text());stack=[(structure(data,True),'')];counts=Counter();audits=Counter();maximum=0;batch=[];futures=set()
 def collect(done):
  for f in done:audits.update(f.result())
 with ProcessPoolExecutor(max_workers=workers,mp_context=multiprocessing.get_context('spawn'))as pool:
  for idx,node in enumerate(data['nodes']):
   box,path=stack.pop();counts[node['kind']]+=1;maximum=max(maximum,len(path))
   if node['kind']=='S':
    a,b=tp.halve(box,node['axis']);stack.extend([(b,path+'1'),(a,path+'0')])
   elif node['kind']!='O':batch.append((box,node,idx,path))
   if len(batch)>=(1 if node['kind']in ('W40','U41','G41','B42','C42','B44')else 128):
    futures.add(pool.submit(check_chunk,(backend,batch)));batch=[]
    if len(futures)>=2*workers:
     done,futures=wait(futures,return_when=FIRST_COMPLETED);collect(done)
  if batch:futures.add(pool.submit(check_chunk,(backend,batch)))
  while futures:
   done,futures=wait(futures,return_when=FIRST_COMPLETED);collect(done)
 assert not stack and audits['checked']==sum(v for k,v in counts.items()if k not in ('S','O'))
 assert len(data['nodes'])==2*counts['S']+1 and audits['EMPTY']+audits['SAFE']+counts['O']==counts['S']+1
 assert audits['B44_local_O']==0 and sha(tree)==tree_sha
 if counts['O']and not allow_open:raise ValueError('Unpaid root frontiers')
 return {'status':'PARTIAL_EXACT_COVERAGE_ONLY'if counts['O']else'COMPLETE_ALPHA_COVERAGE','nodes':len(data['nodes']),'splits':counts['S'],'contradictions':audits['EMPTY'],'alpha_safe':audits['SAFE'],'open':counts['O'],'max_depth':maximum,'kinds':dict(counts),'terminal_audit':dict(audits),'tree_sha256':tree_sha,'model_sha256':data['model_sha256'],'source_manifest_sha256':sha(ROOT/'R54_SOURCE_MANIFEST.json'),'r54_binding':binding(),'backend':backend,'workers':workers,'seconds':time.monotonic()-start,'whole_B_closed':not counts['O'],'macro_ledger':'14/15','controller_only_may_book_completion':True,'scope':'All actual original siblings and root splits retained. B44 internal24-image splits count separately. B44 uses its strict isolated frozen Fraction acceptor with dense prefix/terminal checks on both backends; old Fraction cold adds U41 dense checks.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--tree',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--workers',type=int,default=40);p.add_argument('--backend',choices=('native','fraction'),default='native');p.add_argument('--allow-open',action='store_true');a=p.parse_args()
 if not 1<=a.workers<=40:raise ValueError('40-worker cap')
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 if a.out.exists():raise ValueError('Immutable receipt exists')
 r=replay(a.tree,a.workers,a.backend,a.allow_open);a.out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
