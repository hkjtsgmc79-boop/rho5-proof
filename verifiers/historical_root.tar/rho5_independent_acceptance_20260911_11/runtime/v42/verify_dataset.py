"""Replay received partial certificates, new complete parents, and diagnostic covers.
No original large tree is present. No solver or discovery is called.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse,gzip,json,multiprocessing as mp,time
from _v42_bootstrap import ROOT,prepare,v41_api,centers,canonical_hash
import bound_protocol as bp
import transport_box as tb
S=None

def init():
 global S
 S=json.loads((prepare()['handoff']/'round51/REMAINING_SAMPLES64.json').read_text())

def job(j):
 mode,entry=j;vp,db,sa=v41_api()
 if mode=='port':
  i=entry;s=S[i];node=json.loads((ROOT/f'certificates/port_{i:02}.json').read_text())
  if node['prefix']!=s['partial_certificate']:raise ValueError('Incoming prefix replaced')
  val=bp.verify(s['box'],node,allow_open=True,cross_check=True)
  if val['status']!='OPEN':raise ValueError('Unexpected diagnostic credit; update report')
  attempts=val['port']['attempts'];dl=[];scores=[]
  for att in attempts:
   branchbest=[]
   for b in att['branches']:
    if b['status']=='EMPTY_BRANCH':continue
    dl.extend(Q(c['distance_lower'])for c in b['centers'])
    branchbest.append(min(Q(c['score_upper'])for c in b['centers']))
   if branchbest:scores.append(max(branchbest))
  val['diagnostic']={'sample':i,'index':s['index'],'all_operation_cubes_disjoint':bool(dl)and min(dl)>tb.RHO,
      'distance_lower_all':str(min(dl))if dl else None,'best_worst_branch_score_upper':str(min(scores))if scores else None}
  val['sample']=i
  return mode,val
 if mode=='composed':
  i=entry;s=S[i];node=json.loads((ROOT/f'certificates/composed_{i:02}.json').read_text())
  if node['prefix']!=s['partial_certificate']:raise ValueError('Composed incoming prefix')
  val=bp.verify(s['box'],node,allow_open=True,cross_check=True);val.update(sample=i,index=s['index'])
  return mode,val
 if mode=='closed':
  i=entry;s=S[i];node=json.loads((ROOT/f'certificates/closed_{i:02}.json').read_text())
  old=s['partial_certificate']['trace']['waves'];new=node['trace']['waves']
  if new[:len(old)]!=old:raise ValueError('Old exact prefix not preserved')
  val=vp.verify(s['box'],node,allow_open=False,cross_check=True)
  if val['status']!='EMPTY':raise ValueError('Complete parent not empty')
  return mode,dict(sample=i,index=s['index'],**val,retained_waves=len(old),retained_bounds=sum(map(len,old)),
      added_waves=len(new)-len(old),added_bounds=sum(map(len,new))-sum(map(len,old)))
 if mode=='profile':
  f=ROOT/entry;meta=json.loads(f.with_suffix('.comparison.json').read_text());s=S[meta['sample']]
  val=vp.verify(s['box'],json.loads(f.read_text()),allow_open=True,cross_check=True)
  for k in ('status','waves','bounds'):
   if val[k]!=meta[k]:raise ValueError('Profile receipt '+k)
  return mode,dict(sample=meta['sample'],profile=meta['profile'],**val)
 if mode=='budget':
  i=entry;s=S[i];f=ROOT/f'evidence/budget_traces/s{i:02}.json';meta=json.loads(f.with_suffix('.result.json').read_text())
  val=vp.verify(s['box'],json.loads(f.read_text()),allow_open=True,cross_check=True)
  for k in ('status','waves','bounds'):
   if val[k]!=meta[k]:raise ValueError('Budget receipt '+k)
  return mode,dict(sample=i,**val)
 raise ValueError('job kind')

def run(jobs=4):
 st=time.monotonic();selection=json.loads((ROOT/'controls/sample_selection.json').read_text())
 work=[('port',i)for i in selection['structural_sample_ordinals']]
 work += [('composed',i)for i in selection['conditional_samples']]
 work += [('closed',i)for i in selection['complete_parent_samples']]
 for p in (ROOT/'evidence/profile_traces').glob('s*.json'):
  if p.name.endswith('.comparison.json') or '.receipt.' in p.name:continue
  work.append(('profile',str(p.relative_to(ROOT))))
 work += [('budget',i)for i in selection['budget_extension_samples']if i not in selection['complete_parent_samples']]
 with mp.Pool(jobs,initializer=init)as pool:ans=list(pool.imap_unordered(job,work))
 grouped={k:[v for mode,v in ans if mode==k]for k in('port','composed','closed','profile','budget')}
 expected=json.loads((ROOT/'evidence/verified_enclosures.json').read_text())['results']
 for v in grouped['port']:
  e=next(x for x in expected if x['sample']==v['sample'])
  if v['endpoint_sha256']!=canonical_hash(e['aux_image']):raise ValueError('Exact endpoint differs from saved discovery enclosure')
 root=prepare()['handoff'];frontiers=[json.loads(x)for x in gzip.open(root/'round51/checkpoint/OPEN_FRONTIERS.jsonl.gz','rt')if x.strip()]
 cs=centers();assert all(c[0]==cs[0][0]for c in cs);kc=Q(cs[0][0]);kcounters={'below':0,'above':0,'overlaps':0}
 for f in frontiers:
  lo,hi=map(Q,f['box'][0]);c='below'if hi<kc-tb.RHO else'above'if lo>kc+tb.RHO else'overlaps';kcounters[c]+=1
 if len(frontiers)!=923 or kcounters!={'below':254,'above':85,'overlaps':584}:raise ValueError('Source box/cube invariant diagnosis')
 byidx={x['index']:x for x in frontiers};insertion=json.loads((ROOT/'INSERTION_INDEX.json').read_text())
 if len(set(x['index']for x in insertion))!=3:raise ValueError('Duplicate insertion target')
 for v in insertion:
  if v['index']not in byidx or byidx[v['index']]['path']!=v['path']or byidx[v['index']]['box']!=v['box']:raise ValueError('Not a received open frontier')
 cold=json.loads((root/'round51/receipts/COLD_REPLAY.json').read_text());warm=json.loads((root/'round51/receipts/FROZEN_ROOT_REPLAY.json').read_text())
 for k in ('nodes','splits','open','contradictions','alpha_safe','tree_sha256','model_sha256','source_manifest_sha256'):
  if cold[k]!=warm[k]:raise ValueError('Received receipt disagreement '+k)
 if cold['tree_sha256']!=bp.ROUND51_ROOT or cold['open']!=923:raise ValueError('Received final version')
 summary=dict(status='V42_RECEIVED_ENDPOINTS_AND_NEW_PARENT_CERTIFICATES_PASS',
  received_manifest_files=prepare()['manifest_count'],structural_cases=len(grouped['port']),
  local_safe_parent_hits=sum(x['status']=='SAFE_ALPHA'for x in grouped['port']),
  cheap_B01_high_empty_hits=sum(x['cheap']['status']=='EMPTY_HIGH'for x in grouped['port']),
  disjoint_transport_families=sum(x['diagnostic']['all_operation_cubes_disjoint']for x in grouped['port']),
  k_obstruction=kcounters,conditional_parents=grouped['composed'],new_complete_parents=grouped['closed'],
  new_complete_count=len(grouped['closed']),profile_traces_verified=len(grouped['profile']),budget_partial_traces_verified=len(grouped['budget']),
  unreceived_original_tree_replayed=False,macro_ledger='14/15',seconds=time.monotonic()-st)
 if summary['new_complete_count']!=3 or summary['disjoint_transport_families']!=15:raise ValueError('Unexpected verified credit')
 return summary,grouped
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--jobs',type=int,default=4);ap.add_argument('--output');a=ap.parse_args()
 summary,details=run(a.jobs)
 if a.output:Path(a.output).write_text(json.dumps({'summary':summary,'details':details},indent=2)+'\n')
 print(json.dumps(summary))
