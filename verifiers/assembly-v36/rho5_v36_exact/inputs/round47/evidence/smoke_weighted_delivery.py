#!/usr/bin/env python3
"""Exercise H in the full/light export, portable replay and raw-tree restoration."""
from pathlib import Path
import json,hashlib,shutil,subprocess,sys,os
own=Path('/root/microscope_ws/rho5_cqg_v35_low_alpha_20260908/attempt_01')
src=own/'working_weighted_height';base=own/'delivery_smoke_h_v1';base.mkdir();work=base/'package';work.mkdir();(base/'tmp').mkdir()
sys.path.insert(0,str(src/'discovery'));import frontier_parallel as fp
manifest=json.loads((src/'MANIFEST.json').read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
for n,h in manifest['files'].items():
 assert sha(src/n)==h,n
 if Path(n).name in ('checkpoint.tree','checkpoint.tree.gz'):continue
 p=work/n;p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,p)
fixture=json.loads((src/'tests/weighted_height_controls.json').read_text())[0]
state={'status':'SOFTWARE_SMOKE_ONLY_NO_RESEARCH_CREDIT','models':{},'expected_models':['I_LOW_ALPHA','II_LOW_ALPHA'],'workers_cap':40,'ledger':'11/15'}
for name in state['expected_models']:
 p=work/'models'/name/'checkpoint.tree'
 if name=='I_LOW_ALPHA':p.write_text('O\n')
 else:shutil.copy2(src/'weighted_height_test_artifacts'/(fixture['id']+'.tree'),p)
 result=fp.run_verify(src/'models'/name/'verify',p)
 assert result['open']>0
 assert result['weighted_height_leaves']==(1 if name=='II_LOW_ALPHA' else 0)
 state['models'][name]={**result,'model_sha256':sha(p.parent/'model.json'),'tree':str(p),'tree_sha256':sha(p)}
dump(work/'MANIFEST.json',{'scope':'software smoke with one H fixture and unpaid roots; no research credit',
 'files':{str(p.relative_to(work)):sha(p) for p in work.rglob('*') if p.is_file()}})
s=work/'campaign_low_alpha/CURRENT_STATE.json';s.parent.mkdir();dump(s,state)
(base/'FINAL_GAP_REPORT.md').write_text('Software test only: I is O, II has one known H fixture with all unpaid ancestral siblings. This is not the research campaign or its completion.\n')
env=os.environ.copy();env.update(TMPDIR=str(base/'tmp'),OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1',
 CPLUS_INCLUDE_PATH='/root/microscope_ws/controller_v31_review_20260907.cRz00v/deps/usr/include')
commands=[
 [sys.executable,str(own/'audit_frontiers.py'),'--package',str(work),'--state',str(s),'--out',str(base/'final_frontier_audit')],
 [sys.executable,str(own/'make_final_delivery.py'),'--package',str(work),'--out',str(base/'delivery'),'--allow-partial']]
for i,cmd in enumerate(commands):
 p=subprocess.run(cmd,env=env,text=True,capture_output=True);(base/f'phase_{i}.log').write_text(p.stdout+p.stderr);assert p.returncode==0,p.stderr
full=base/'delivery/rho5_round47_alpha';portable=json.loads((base/'delivery/PORTABLE_COLD_REPLAY_RESULT.json').read_text())
assert portable['models']['II_LOW_ALPHA']['weighted_height_leaves']==1
commands=[
 [sys.executable,str(full/'restore_state.py')],
 [sys.executable,str(full/'source/verify_campaign.py'),str(full/'source/campaign_low_alpha/CURRENT_STATE.json'),'--allow-open'],
 [sys.executable,str(full/'source/run_campaign.py'),'--prepare-only','--models','I_LOW_ALPHA','II_LOW_ALPHA','--output',str(full/'source/campaign_low_alpha')]]
for i,cmd in enumerate(commands,2):
 p=subprocess.run(cmd,env=env,text=True,capture_output=True);(base/f'phase_{i}.log').write_text(p.stdout+p.stderr);assert p.returncode==0,p.stderr
restored=json.loads((full/'source/campaign_low_alpha/CURRENT_STATE.json').read_text())
assert restored['models']['II_LOW_ALPHA']['weighted_height_leaves']==1
assert all(Path(r['tree']).suffix=='.tree' for r in restored['models'].values())
result={'status':'WEIGHTED_H_DELIVERY_PORTABLE_REPLAY_AND_RESUME_SMOKE_PASS','research_credit':False,
 'test_roots':'I is O; II is one known H with unpaid siblings','weighted_height_count_preserved':1,
 'no_actual_campaign_mutation':True,'directory':str(base)}
dump(own/'WEIGHTED_DELIVERY_SMOKE_RESULT.json',result);print(json.dumps(result,indent=2))
