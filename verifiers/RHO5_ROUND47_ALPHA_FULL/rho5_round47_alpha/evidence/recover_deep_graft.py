#!/usr/bin/env python3
"""Recover all accepted worker checkpoints after a transport recursion limit.

No mathematics or source rules change. The C++ certificate depth cap stays 512.
Two nested traversals may both hold a legitimate 500-level original-root path,
so the Python transport must permit more than the default 1000 frames.
"""
from pathlib import Path
import sys,json,hashlib,importlib,datetime
root=Path('/root/microscope_ws/rho5_cqg_v35_low_alpha_20260908/attempt_01')
work=root/'working_direct_f';mod=work/'discovery/frontier_parallel.py'
old=mod.read_text();marker='# CQG nested original-root graft: each valid path is <=512, two may coexist.'
if marker not in old:
    before='PINS={}  # populated from new immutable models by run_campaign.py'
    assert old.count(before)==1
    (root/'frontier_parallel_before_recursion_fix.py').write_text(old)
    mod.write_text(old.replace(before,marker+'\nsys.setrecursionlimit(max(sys.getrecursionlimit(),4096))\n'+before))
    manifest=json.loads((work/'MANIFEST.json').read_text())
    copy=work/'reference/DIRECT_F_PRE_GRAFT_FIX_MANIFEST.json';copy.write_text(json.dumps(manifest,indent=2)+'\n')
    manifest['files']['reference/DIRECT_F_PRE_GRAFT_FIX_MANIFEST.json']=hashlib.sha256(copy.read_bytes()).hexdigest()
    manifest['files']['discovery/frontier_parallel.py']=hashlib.sha256(mod.read_bytes()).hexdigest()
    (work/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
sys.path.insert(0,str(work));sys.path.insert(0,str(work/'discovery'))
import run_campaign as rc
import frontier_parallel as fp
fp.PINS={n:rc.prepare(n) for n in ('I_LOW_ALPHA','II_LOW_ALPHA')}
wave=work/'campaign_low_alpha/wave_0001'
manifest=json.loads((wave/'FRONTIER_MANIFEST.json').read_text())
result=fp.graft_wave(work,wave,manifest['jobs'],manifest)
state={'status':'COMPLETE_SELECTED_ORIGINAL_ROOTS' if all(v['open']==0 for v in result.values()) else 'EXACT_PARTIAL_ORIGINAL_ROOTS',
       'expected_models':['I_LOW_ALPHA','II_LOW_ALPHA'],'models':result,'workers_cap':40,'ledger':'11/15'}
fp.write_json(work/'campaign_low_alpha/CURRENT_STATE.json',state)
receipt={'status':'ALL_ACCEPTED_FRONTIERS_RECOVERED_AND_ORIGINAL_ROOTS_REPLAYED',
         'recovered_wave':str(wave),'worker_checkpoints_discarded':0,
         'python_transport_recursion_limit':sys.getrecursionlimit(),'cpp_proof_depth_cap':512,
         'model_and_rule_changed':False,'recovery_time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'models':{n:{k:v[k] for k in ('nodes','contradiction_leaves','alpha_safe_leaves','open','max_depth','model_sha256','tree_sha256')} for n,v in result.items()}}
fp.write_json(root/'DEEP_GRAFT_RECOVERY_RESULT.json',receipt);print(json.dumps(receipt,indent=2))
