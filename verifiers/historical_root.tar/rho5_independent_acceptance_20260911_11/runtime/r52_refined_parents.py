"""Small, explicit stall cohort; improved discovery with unchanged U41 acceptance."""
from pathlib import Path
from collections import Counter
from concurrent.futures import ProcessPoolExecutor,as_completed
import argparse,copy,json,multiprocessing,os,random,time
from r52_condition_probe import refined,v41_api
ROOT=Path(__file__).resolve().parent
def read(p):return json.loads(p.read_text())
def write(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
def worker(payload):
 src,outdir=payload
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 start=time.monotonic();deadline=start+90;vp,db,sa=v41_api()
 node=copy.deepcopy(src['partial_certificate']);box=src['box'];profile=node['trace']['profile']
 val=vp.verify(box,node,True,True);assert val['status']=='OPEN'
 out=db.common_contract(sa.fs.parent_enclosure(box),profile=profile)
 for wave in node['trace']['waves']:out=db.apply_wave(out,wave,profile=profile,cross_check=True)
 nw=len(node['trace']['waves']);nb=sum(map(len,node['trace']['waves']));stats=Counter();reason='additional_wave_budget';path=Path(outdir)/f"certificate_{src['index']:07d}.json"
 write(path,node)
 for turn in range(9):
  if out['status']=='EMPTY':node['trace']['terminal']={'kind':'I'};reason='certified_terminal';break
  if sa.fs.safe_port(out['aux_image'])is not None:node['trace']['terminal']={'kind':'A'};reason='certified_terminal';break
  if time.monotonic()>=deadline:reason='soft_budget';break
  rows,boxes=db.rows_and_bounds(out['aux_image'],profile=profile);term,wave=refined(rows,boxes,deadline,stats)
  if term:node['trace']['terminal']=term;reason='certified_terminal';break
  if turn==8:break
  if not wave:reason='no_positive_exact_refined_bound';break
  nxt=db.apply_wave(out,wave,profile=profile,cross_check=True)
  if nxt==out:reason='outward_grid_fixed_point';break
  node['trace']['waves'].append(wave);out=nxt;write(path,node)
 exact=vp.verify(box,node,True,True);write(path,node)
 receipt={**exact,'discovery_reason':reason,'prior_waves':nw,'prior_bounds':nb,'added_waves':len(node['trace']['waves'])-nw,
  'added_bounds':sum(map(len,node['trace']['waves']))-nb,'proposal_diagnostics':dict(stats)}
 rec={**src,'status':exact['status'],'node':node if exact['status']!='OPEN'else None,'partial_certificate':node if exact['status']=='OPEN'else None,
  'receipt':receipt,'profile':profile,'seconds':time.monotonic()-start,'source_phase':'refined_stall32'}
 write(Path(outdir)/f"result_{src['index']:07d}.json",rec)
 return {'index':src['index'],'status':exact['status'],'reason':reason,'seconds':rec['seconds'],'added_waves':receipt['added_waves'],'added_bounds':receipt['added_bounds']}
def main(workers):
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 assert (ROOT/'base24_remaining760/RESULT.json').exists(),'finish the baseline continuation before selecting the stall cohort'
 out=ROOT/'refined_stall32';out.mkdir();closed=set();latest={}
 for name in ('seeds','matched_base24','matched_pc24','base24_remaining760'):
  for p in (ROOT/name).glob('result_*.json'):
   r=read(p)
   if r['status']!='OPEN':closed.add(r['index'])
   else:latest[r['index']]=r
 closed.update(r['index']for r in read(ROOT/'v42/INSERTION_INDEX.json'))
 candidates={i:r for i,r in latest.items()if i not in closed and r['receipt']['discovery_reason']=='no_retained_proposal'}
 priority=[i for i in (144782,564048,491229,674450)if i in candidates]
 rest=sorted(set(candidates)-set(priority));selected=priority+random.Random(524281).sample(rest,min(32-len(priority),len(rest)))
 records=[candidates[i]for i in selected];write(out/'INPUT.json',{'candidate_population':len(candidates),'selected':len(records),'priority_indices':priority,
  'selection':'four explicitly persistent examples plus deterministic random remainder among latest no_retained_proposal parents; not a population-rate sample',
  'additional_wave_cap':8,'seconds_per_parent':90,'records':records})
 start=time.monotonic();done=[]
 with ProcessPoolExecutor(max_workers=workers,mp_context=multiprocessing.get_context('spawn'))as pool:
  for f in as_completed([pool.submit(worker,(r,str(out)))for r in records]):
   done.append(f.result())
   if len(done)%8==0:print(json.dumps({'done':len(done),'total':len(records),'closed':sum(r['status']!='OPEN'for r in done),'seconds':time.monotonic()-start}),flush=True)
 result={'status':'R52_REFINED_STALL_COHORT_COMPLETE','evaluated':len(done),'workers':workers,'outcomes':dict(Counter(r['status']for r in done)),
  'stop_reasons':dict(Counter(r['reason']for r in done)),'added_waves':sum(r['added_waves']for r in done),'added_bounds':sum(r['added_bounds']for r in done),
  'worker_elapsed_sum':sum(r['seconds']for r in done),'wall_seconds':time.monotonic()-start,'whole_B_closed':False,'macro_ledger':'14/15'}
 write(out/'RESULT.json',result);print(json.dumps(result,indent=2))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--workers',type=int,default=32);a=p.parse_args();assert 1<=a.workers<=40;main(a.workers)
