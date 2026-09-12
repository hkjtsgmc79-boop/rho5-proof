#!/usr/bin/env python3
"""Validate and optionally install a first-visit one-solve scheduling sieve."""
from pathlib import Path
import argparse,json,hashlib,importlib.util,fcntl,shutil,time
ap=argparse.ArgumentParser();ap.add_argument('--apply',action='store_true');args=ap.parse_args()
own=Path('/root/microscope_ws/rho5_cqg_v35_low_alpha_20260908/attempt_01')
root=own/'working_flow_tube';path=root/'discovery/frontier_parallel.py'
old=path.read_text();oldsha=hashlib.sha256(old.encode()).hexdigest()
needle="str(seconds),'1000000',job['focus']"
assert old.count(needle)==1,'Unexpected or already changed source'
new=old.replace(needle,"str(seconds),str(1 if job['rounds']==1 else 1000000),job['focus']")
needle2="search_seconds=seconds,focus=job['focus'],rounds=job['rounds'],scope="
assert new.count(needle2)==1
new=new.replace(needle2,"search_seconds=seconds,search_max_solves=1 if job['rounds']==1 else 1000000,focus=job['focus'],rounds=job['rounds'],scope=")
newsha=hashlib.sha256(new.encode()).hexdigest()
controls=own/'first_sieve_controls';receipt=own/'FIRST_SOLVE_SIEVE_TESTS.json'
if not args.apply:
 controls.mkdir();private=controls/'frontier_parallel_candidate.py';private.write_text(new)
 spec=importlib.util.spec_from_file_location('sieve_candidate',private);fp=importlib.util.module_from_spec(spec);spec.loader.exec_module(fp)
 samples=json.loads((own/'weighted_alpha_probe/SAMPLES.json').read_text())['jobs'];samples={j['id']:j for j in samples}
 rows=[json.loads(s) for s in (own/'weighted_alpha_probe/RESULTS.jsonl').read_text().splitlines()]
 selected=[r for r in rows if r['closed_contradiction']][:3]+[r for r in rows if r['height_t']>0 and not r['closed_contradiction']]
 records=[]
 for i,row in enumerate(selected):
  j=dict(samples[row['id']]);d=controls/f'control_{i}';d.mkdir();j.update(directory=str(d),rounds=0)
  (d/'checkpoint.tree').write_bytes(fp.envelope(j['steps']))
  start=time.monotonic();first=fp.job_chunk(j,root,1.0)
  assert first['search_max_solves']==1 and first['rounds']==1
  assert first['open']>=len(j['steps'])
  if row['closed_contradiction']:assert first['target_open']==0
  second=None
  if first['target_open']>0:
   assert first['target_open']<=2
   second=fp.job_chunk(j,root,.05)
   assert second['search_max_solves']==1000000 and second['rounds']==2
   assert second['open']>=len(j['steps'])
  records.append({'id':row['id'],'first':first,'second':second,'seconds':time.monotonic()-start})
 assert any(r['second'] is not None for r in records),'Need an unpaid branch continuation control'
 result={'status':'FIRST_SOLVE_SIEVE_CONTROLS_PASSED','old_source_sha256':oldsha,'new_source_sha256':newsha,
         'controls':records,'mathematical_acceptor_changed':False,'all_siblings_preserved':True,
         'semantics':'first visit max_solves=1; all subsequent visits retain max_solves=1000000 and original watchdog'}
 receipt.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='controls'},indent=2))
else:
 result=json.loads(receipt.read_text())
 assert result['status']=='FIRST_SOLVE_SIEVE_CONTROLS_PASSED'
 assert result['old_source_sha256']==oldsha and result['new_source_sha256']==newsha
 with (root/'.campaign.lock').open('a') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
  manifest=json.loads((root/'MANIFEST.json').read_text())
  for n,h in manifest['files'].items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h,n
  shutil.copy2(path,own/'frontier_parallel_before_first_sieve.py')
  shutil.copy2(root/'MANIFEST.json',root/'reference/PRE_FIRST_SOLVE_SIEVE_MANIFEST.json')
  path.write_text(new)
  manifest['files']['discovery/frontier_parallel.py']=newsha
  rel='reference/PRE_FIRST_SOLVE_SIEVE_MANIFEST.json'
  manifest['files'][rel]=hashlib.sha256((root/rel).read_bytes()).hexdigest()
  (root/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
  change={'status':'FIRST_SOLVE_SIEVE_INSTALLED_IDLE_WRITER_LOCK_HELD','old_source_sha256':oldsha,
          'new_source_sha256':newsha,'mathematical_acceptor_changed':False,'model_files_changed':False,
          'proof_credit_added_by_installation':0,'tests_sha256':hashlib.sha256(receipt.read_bytes()).hexdigest()}
  (own/'FIRST_SOLVE_SIEVE_CHANGE.json').write_text(json.dumps(change,indent=2)+'\n');print(json.dumps(change,indent=2))
