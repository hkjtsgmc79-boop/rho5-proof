#!/usr/bin/env python3
"""Adopt every latest accepted parent leaf after its writer stops; reprove I cold."""
from pathlib import Path
import json,hashlib,shutil,subprocess,sys,os,fcntl,time
own=Path('/root/microscope_ws/rho5_cqg_v35_low_alpha_20260908/attempt_01')
src=own/'working_flow_tube';dst=own/'working_weighted_height';names={'I_LOW_ALPHA','II_LOW_ALPHA'}
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
def dump(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
oldlock=(src/'.campaign.lock').open('a');fcntl.flock(oldlock,fcntl.LOCK_EX|fcntl.LOCK_NB)
newlock=(dst/'.campaign.lock').open('a');fcntl.flock(newlock,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert not (dst/'campaign_low_alpha/CURRENT_STATE.json').exists(),'Already adopted; do not overwrite'
tests=json.loads((dst/'weighted_height_test_artifacts/RESULT.json').read_text())
assert tests['status']=='WEIGHTED_HEIGHT_EXACT_CONTROLS_PASSED'
regression=json.loads((own/'WEIGHTED_ALPHA_REGRESSION.json').read_text())
assert regression['status']=='V35_EXACT_ALPHA_EXIT_CODES_AND_ORIGINAL_ROOT_DEMONSTRATION_PASS'
assert regression['code_comparisons']==1408
manifest=json.loads((dst/'MANIFEST.json').read_text())
for n,h in manifest['files'].items():assert sha(dst/n)==h,n
parent=json.loads((src/'campaign_low_alpha/CURRENT_STATE.json').read_text())
assert set(parent['models'])==names
assert parent['models']['I_LOW_ALPHA']['open']==0
for n,v in parent['models'].items():
 assert Path(v['tree']).resolve().is_relative_to(src/'campaign_low_alpha')
 assert sha(v['tree'])==v['tree_sha256']
 data=json.loads((dst/'models'/n/'model.json').read_text())
 assert v['model_sha256']==data['previous_version_model_sha256']
 assert tests['models'][n]==regression['models'][n]==sha(dst/'models'/n/'model.json')
env=os.environ.copy();env.update(OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1',
 CPLUS_INCLUDE_PATH='/root/microscope_ws/controller_v31_review_20260907.cRz00v/deps/usr/include',TMPDIR=str(own/'tmp'))
print(json.dumps({'event':'new_weighted_model_I_cold_replay_started','parent_open':{n:v['open'] for n,v in parent['models'].items()}}),flush=True)
start=time.monotonic()
p=subprocess.run([sys.executable,str(dst/'verify_task.py'),str(dst/'models/I_LOW_ALPHA'),
                  '--tree',parent['models']['I_LOW_ALPHA']['tree']],env=env,capture_output=True,text=True)
(own/'WEIGHTED_HEIGHT_I_COLD_REPLAY.log').write_text(p.stdout+p.stderr)
assert p.returncode==0,p.stderr
cold=json.loads(p.stdout);assert cold['open']==0 and cold['weighted_height_leaves']==0
assert cold['model_sha256']==tests['models']['I_LOW_ALPHA']
dump(own/'WEIGHTED_HEIGHT_I_COLD_REPLAY.json',cold)
accepted={}
for n,v in parent['models'].items():
 target=dst/'campaign_low_alpha/inherited'/f'{n}.tree';target.parent.mkdir(parents=True,exist_ok=True)
 shutil.copy2(v['tree'],target);assert sha(target)==v['tree_sha256']
 if n=='I_LOW_ALPHA':record=dict(cold)
 else:
  record={k:x for k,x in v.items() if k not in ('strict_original_acceptance','semantic_cold_replay')}
  record.update(status='INHERITED_ORIGINAL_TREE_PENDING_NEW_II_KERNEL_REPLAY',weighted_height_leaves=0)
 record.update(tree=str(target),tree_sha256=v['tree_sha256'],model_sha256=tests['models'][n],
               parent_model_sha256=v['model_sha256'],original_root_accepted=(n=='I_LOW_ALPHA'),
               original_roots_and_rows_unchanged=True,new_coverage_credit_from_adoption=0)
 accepted[n]=record
state={'status':'INHERITED_CHECKPOINT_PENDING_II_NEW_KERNEL_REPLAY','expected_models':sorted(names),
       'models':accepted,'workers_cap':40,'ledger':'11/15'}
dump(dst/'campaign_low_alpha/CURRENT_STATE.json',state)
dump(own/'WEIGHTED_HEIGHT_PARENT_STATE.json',parent)
receipt={'status':'LATEST_TWO_ORIGINAL_ROOTS_ADOPTED_I_REPROVED_II_NEW_REPLAY_REQUIRED',
 'parent_source':str(src),'working':str(dst),'parent_state_sha256':sha(src/'campaign_low_alpha/CURRENT_STATE.json'),
 'source_manifest_sha256':sha(dst/'MANIFEST.json'),'old_and_new_tree_hashes_identical':True,
 'models':{n:{k:v[k] for k in ('nodes','contradiction_leaves','alpha_safe_leaves','open','tree_sha256','model_sha256','parent_model_sha256')} for n,v in accepted.items()},
 'I_cold_replay_sha256':sha(own/'WEIGHTED_HEIGHT_I_COLD_REPLAY.json'),
 'II_replay_mandatory_before_next_search':True,'new_coverage_credit':0,'seconds':time.monotonic()-start}
dump(own/'WEIGHTED_HEIGHT_ADOPTION.json',receipt);print(json.dumps(receipt,indent=2),flush=True)
