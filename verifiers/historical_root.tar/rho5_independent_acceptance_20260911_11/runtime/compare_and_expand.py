from pathlib import Path
from collections import Counter
import csv,gzip,json
ROOT=Path(__file__).resolve().parent
def read(p):return json.loads(p.read_text())
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
A={r['index']:r for r in map(read,(ROOT/'matched_base24').glob('result_*.json'))}
B={r['index']:r for r in map(read,(ROOT/'matched_pc24').glob('result_*.json'))}
assert len(A)==len(B)==64 and set(A)==set(B)
oldcost=Counter()
with (ROOT/'inherited/ROUND51_FRAME_RESULTS.csv').open()as f:
 for r in csv.DictReader(f):
  if r['profile']=='BASE':oldcost[int(r['index'])]+=float(r['seconds'])
details=[]
for idx in sorted(A):
 a,b=A[idx],B[idx];assert a['path']==b['path']and a['box']==b['box']
 s=read(ROOT/'seeds'/f'result_{idx:07d}.json');old=s['partial_certificate']['trace']
 assert old['profile']=='BASE'and len(old['waves'])==12
 at=a['node']or a['partial_certificate'];assert at['trace']['waves'][:12]==old['waves']
 details.append({'index':idx,'base_status':a['status'],'pc_status':b['status'],'base_prior_worker_elapsed':oldcost[idx],
 'base_incremental_worker_elapsed':a['seconds'],'base_cumulative_worker_elapsed':oldcost[idx]+a['seconds'],
 'pc_fresh_worker_elapsed':b['seconds'],'base_reused_waves':12,'base_added_waves':a['receipt']['waves']-12,
 'base_reused_bounds':sum(map(len,old['waves'])),'base_added_bounds':a['receipt']['bounds']-sum(map(len,old['waves'])),
 'base_total_waves':a['receipt']['waves'],'pc_total_waves':b['receipt']['waves']})
ac={i for i,r in A.items()if r['status']!='OPEN'};bc={i for i,r in B.items()if r['status']!='OPEN'}
r={'status':'R52_MATCHED_SAME_FRAME_SAME_TOTAL_WAVE_COMPARISON','frames':64,'total_wave_cap':24,
 'BASE_closed':len(ac),'PIVOT_CYCLE_closed':len(bc),'both_closed':len(ac&bc),'BASE_only':sorted(ac-bc),'PC_only':sorted(bc-ac),
 'union_closed':len(ac|bc),'base_prior_worker_elapsed':sum(d['base_prior_worker_elapsed']for d in details),
 'base_incremental_worker_elapsed':sum(d['base_incremental_worker_elapsed']for d in details),
 'base_cumulative_worker_elapsed':sum(d['base_cumulative_worker_elapsed']for d in details),
 'pc_fresh_worker_elapsed':sum(d['pc_fresh_worker_elapsed']for d in details),
 'worker_elapsed_is_not_measured_CPU_time':True,'BASE_reused_original_prefix_PC_fresh_profile':True,
 'all_completed_without_soft_budget':all(x['receipt']['discovery_reason']!='soft_budget'for x in list(A.values())+list(B.values())),
 'interpretation':'Comparison of deployed profile workflows at equal total wave caps; retained BASE prefix is charged separately. Finite selected population, not universal dominance.',
 'details':details}
write(ROOT/'MATCHED_COMPARISON.json',r)
known={s['index']for s in read(ROOT/'inherited/ROUND51_SAMPLES64.json')};picked=[]
for f in map(json.loads,gzip.open(ROOT/'graft3/OPEN_FRONTIERS.jsonl.gz','rt')):
 if f['index']in known or f['index']in A:continue
 s=read(ROOT/'seeds'/f"result_{f['index']:07d}.json")
 if s['profile']=='BASE'and s['receipt']['discovery_reason']=='wave_budget':picked.append(f)
assert len(picked)==760
with gzip.open(ROOT/'base24_remaining760.jsonl.gz','wt')as f:f.writelines(json.dumps(x)+'\n'for x in picked)
print(json.dumps({k:v for k,v in r.items()if k!='details'}|{'BASE_expansion_fresh_frames':len(picked)},indent=2))
