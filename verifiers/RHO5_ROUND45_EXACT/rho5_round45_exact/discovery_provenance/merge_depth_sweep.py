"""Combine independently accepted refinements at one identical frozen frontier list."""
from pathlib import Path
import json, shutil, sys
import frontier_parallel as fp

root=Path(sys.argv[1]).resolve();name='II210_214'
canary=root/'parallel_robust_II210_214/wave_001';sweep=root/'depth_sweep/wave_001';broad=root/'broad_sweep/wave_001'
waves={'canary':canary,'deep_sweep':sweep,'broad_sweep':broad}
assert all((p/'WAVE_DISCOVERY_RESULT.json').exists() for p in waves.values())
original=json.loads((canary/'FRONTIER_MANIFEST.json').read_text())
lookups={}
for label,path in waves.items():
 other=json.loads((path/'FRONTIER_MANIFEST.json').read_text())
 assert original['inputs']==other['inputs'] and original['new_split_count']==other['new_split_count']==0
 lookups[label]={j['focus']:j for j in other['jobs']}
selected=[];choices={**{label:0 for label in waves},'unchanged':0}
for job in original['jobs']:
 candidates=[]
 for label,lookup in lookups.items():
  alt=lookup.pop(job['focus']);assert job['steps']==alt['steps'] and job['model_sha256']==alt['model_sha256']
  status=Path(alt['directory'])/'STATUS.json'
  if status.exists():
   info=json.loads(status.read_text());candidates.append((info['target_open']!=0,-info['leaves'],label,alt))
 if candidates:_,_,label,chosen=min(candidates,key=lambda x:x[:3])
 else:chosen=job;label='unchanged'
 selected.append(chosen);choices[label]+=1
assert all(not d for d in lookups.values())
out=root/'merged_II_after_numerical_repair';out.mkdir()
info=fp.graft_wave(root/'working',out,selected,original)[name]
fp.write_json(out/'MERGE_RECEIPT.json',{'status':'IDENTICAL_ORIGINAL_FRONTIERS_MERGED_AND_EXACT_ACCEPTED',
 'choices':choices,'source_manifests':{str(p/'FRONTIER_MANIFEST.json'):fp.digest(p/'FRONTIER_MANIFEST.json') for p in waves.values()},'model':info})
current=root/'parallel_robust_II210_214/CURRENT_STATE.json';shutil.copy2(current,out/'PRIOR_CANARY_CURRENT_STATE.json')
fp.write_json(current,{'status':'EXACT_PARTIAL_ORIGINAL_ROOT' if info['open'] else 'ORIGINAL_MODEL_ROOT_COMPLETE',
 'models':{name:info},'discovery_proposal':'validated_long_double_v1','merge_receipt':str(out/'MERGE_RECEIPT.json'),
 'whole_height_claim_requires_both_complete':True})
print(json.dumps({'event':'merged_II_original_root_accepted','choices':choices,**{k:info[k] for k in ('nodes','leaves','open','max_depth')}}),flush=True)
