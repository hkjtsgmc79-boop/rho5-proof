"""Four previously unpaid C42 charts: refined proposals, unchanged exact acceptance."""
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
from collections import Counter
import copy,json,multiprocessing,os,sys,time
for n in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[n]='1'
ROOT=Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT/'v42'))
import bound_protocol as bp
from _v42_bootstrap import v41_api
def read(p):return json.loads(p.read_text())
def write(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')

def refined(rows,boxes,deadline,stats):
 import numpy as np
 from scipy.optimize import linprog
 _,db,sa=v41_api();n=len(boxes)
 center=np.array([float((b.lo+b.hi)/2)for b in boxes]);half=np.array([float((b.hi-b.lo)/2)for b in boxes])
 mat=np.zeros((len(rows),n));rhs=np.zeros(len(rows))
 for i,(aa,bb)in enumerate(rows):
  rhs[i]=float(bb)
  for j,c in aa.items():mat[i,j]=float(c)
 bb=rhs-mat@center;aa=mat*half;norm=np.maximum(1e-9,np.maximum(abs(bb),np.max(abs(aa),axis=1)));aa/=norm[:,None];bb/=norm
 opts={'time_limit':2,'primal_feasibility_tolerance':1e-10,'dual_feasibility_tolerance':1e-10,'presolve':False}
 scales=(10**10,10**13,10**16,10**19)
 def weights(res):
  stats['lp_status:'+str(res.status)]+=1
  if not res.success:return []
  raw=-res.ineqlin.marginals/norm
  if not np.all(np.isfinite(raw)):return []
  out=[]
  for sc in scales:
   ws=[[i,max(0,int(round(float(w)*sc)))]for i,w in enumerate(raw)];ws=[v for v in ws if v[1]>0]
   if ws:out.append((sc,ws))
  return out
 # No floating objective threshold decides whether an exact C can be proposed.
 obj=np.zeros(n+1);obj[-1]=1
 res=linprog(obj,A_ub=np.column_stack((aa,-np.ones(len(rows)))),b_ub=bb,bounds=[(-1,1)]*n+[(0,None)],method='highs',options=opts)
 for sc,ws in weights(res):
  rec={'kind':'C','weights':ws};margin=sa.inherited.dual_margin(rows,boxes,rec)
  if margin<0:stats['exact_C']+=1;return rec,[]
 obj=np.zeros(n);obj[23]=-half[23]
 res=linprog(obj,A_ub=aa,b_ub=bb,bounds=[(-1,1)]*n,method='highs',options=opts)
 for sc,ws in weights(res):
  rec={'kind':'H','weights':ws,'objective_weight':sc};margin=sa.inherited.dual_margin(rows,boxes,rec)
  if margin<=0:stats['exact_H']+=1;return rec,[]
 options=[]
 for i in range(24):
  if half[i]<=0:continue
  for sign in (1,-1):
   if time.monotonic()>=deadline:return None,[r for _,r in sorted(options,key=lambda v:-v[0])[:16]]
   obj=np.zeros(n);obj[i]=-sign*half[i]
   res=linprog(obj,A_ub=aa,b_ub=bb,bounds=[(-1,1)]*n,method='highs',options=opts);best=None
   for sc,ws in weights(res):
    rec={'coordinate':i,'direction':sign,'objective_weight':sc,'weights':ws}
    val=db.bound_value(rows,boxes,rec);gain=(boxes[i].hi if sign==1 else -boxes[i].lo)-val
    if gain>0 and (best is None or gain>best[0]):best=(gain,rec)
   if best:
    stats['positive_exact_bounds']+=1;options.append((float(best[0])/max(half[i],1e-300),best[1]))
 return None,[r for _,r in sorted(options,key=lambda v:-v[0])[:16]]

def worker(payload):
 sample,label,seconds,additional=payload
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 start=time.monotonic();deadline=start+seconds;node=read(ROOT/f'v42/certificates/composed_{sample:02}.json')
 data=read(ROOT/f'v42/controls/parent_{sample:02}.json');box=data['box']if isinstance(data,dict)else data
 base=bp.endpoint(box,node['prefix'],True);assert base['status']=='OPEN'
 trace=copy.deepcopy(node['children'][label]);assert trace['terminal']=={'kind':'O'}
 bp.child_replay(base['aux_image'],trace,label,True,True)
 _,db,sa=v41_api();profile=trace['profile'];out=db.common_contract({'status':'BOUNDED','aux_image':base['aux_image']},label,profile)
 for wave in trace['waves']:out=db.apply_wave(out,wave,label,profile,True)
 prior_waves=len(trace['waves']);prior_bounds=sum(map(len,trace['waves']));stats=Counter();reason='additional_wave_budget'
 while True:
  if out['status']=='EMPTY':trace['terminal']={'kind':'I'};reason='certified_terminal';break
  if sa.fs.safe_port(out['aux_image'])is not None:trace['terminal']={'kind':'A'};reason='certified_terminal';break
  if time.monotonic()>=deadline:reason='soft_budget';break
  rows,boxes=db.rows_and_bounds(out['aux_image'],label,profile);term,wave=refined(rows,boxes,deadline,stats)
  if term:trace['terminal']=term;reason='certified_terminal';break
  if len(trace['waves'])>=prior_waves+additional:break
  if not wave:reason='no_positive_exact_refined_bound';break
  nxt=db.apply_wave(out,wave,label,profile,True)
  if nxt==out:reason='outward_grid_fixed_point';break
  trace['waves'].append(wave);out=nxt
 result=bp.child_replay(base['aux_image'],trace,label,True,True)
 return {'sample':sample,'label':label,'trace':trace,'exact':result,'prior_waves':prior_waves,'prior_bounds':prior_bounds,
  'added_waves':len(trace['waves'])-prior_waves,'added_bounds':sum(map(len,trace['waves']))-prior_bounds,
  'stop_reason':reason,'proposal_diagnostics':dict(stats),'seconds':time.monotonic()-start}

def main():
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 out=ROOT/'condition_probe';out.mkdir();jobs=[];start=time.monotonic()
 for sample in (20,63):
  node=read(ROOT/f'v42/certificates/composed_{sample:02}.json')
  jobs += [(sample,label,60,8)for label,t in node['children'].items()if t['terminal']=={'kind':'O'}]
 assert len(jobs)==4
 write(out/'INPUT.json',{'jobs':jobs,'changed_only_discovery':True,'scales':[10**10,10**13,10**16,10**19],'feasibility_tolerance':'1e-10','presolve':False,'original_C42_rule_unchanged':True})
 results=[]
 with ProcessPoolExecutor(max_workers=4,mp_context=multiprocessing.get_context('spawn'))as pool:
  for f in as_completed([pool.submit(worker,j)for j in jobs]):
   r=f.result();results.append(r);write(out/f'chart_{len(results):02}.json',r)
 samples=read(ROOT/'inherited/ROUND51_SAMPLES64.json');parents=[]
 for sample in (20,63):
  node=read(ROOT/f'v42/certificates/composed_{sample:02}.json')
  for r in results:
   if r['sample']==sample:node['children'][r['label']]=r['trace']
  src=samples[sample];ans=bp.verify(src['box'],node,True,True)
  status={'EMPTY_HIGH':'EMPTY','SAFE_ALPHA':'SAFE','OPEN':'OPEN'}[ans['status']]
  rec={**src,'status':status,'node':node if status!='OPEN'else None,'partial_cover':node if status=='OPEN'else None,'receipt':ans,'source':'refined_conditional_four_charts'}
  write(out/f"result_{src['index']:07d}.json",rec);parents.append({'index':src['index'],'sample':sample,**ans})
 summary={'status':'R52_FOUR_CONDITIONAL_CHART_PROBE_COMPLETE','workers':4,'wall_seconds':time.monotonic()-start,'parents':parents,
  'chart_outcomes':dict(Counter(r['exact']['status']for r in results)),'stop_reasons':dict(Counter(r['stop_reason']for r in results)),
  'added_waves':sum(r['added_waves']for r in results),'added_bounds':sum(r['added_bounds']for r in results),
  'whole_B_closed':False,'macro_ledger':'14/15'}
 write(out/'RESULT.json',summary);print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
