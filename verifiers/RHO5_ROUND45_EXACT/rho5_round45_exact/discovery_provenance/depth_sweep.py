"""Pay old numerically stalled deep frontiers while the four broad workers finish.

All files are independent of the running canary. Merge only after both barriers.
"""
from pathlib import Path
import json, os, shutil, sys, time
import frontier_parallel as fp

root=Path(sys.argv[1]).resolve();out=root/'depth_sweep';out.mkdir()
work=out/'working';name='II210_214';model=work/'models'/name;model.mkdir(parents=True)
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
os.environ['TMPDIR']=str(root/'tmp');os.environ['CPLUS_INCLUDE_PATH']='/root/microscope_ws/controller_v31_review_20260907.cRz00v/deps/usr/include'
if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
for fn in ('model.json','scope.json'):shutil.copy2(root/'working/models'/name/fn,model/fn)
(model/'verify').symlink_to(root/'working/models'/name/'verify')
(model/'discover_focus').symlink_to(root/'robust_proposal'/name/'discover_robust')
for fn in ('verify_task.py','build_model.py','make_contact_case.py'):shutil.copy2(root/'working'/fn,work/fn)
(work/'source').symlink_to(root/'working/source',target_is_directory=True)
tree=root/'parallel/wave_001/II210_214_grafted.tree';wave=out/'wave_001'
jobs,manifest=fp.prepare_wave(work,wave,{name:tree},0)
selected=[j for j in jobs if len(j['steps'])>=100]
print(json.dumps({'event':'deep_sweep_started','workers':36,'selected_frontiers':len(selected),'all_frontiers':len(jobs)}),flush=True)
fp.execute_wave(work,wave,selected,36,time.monotonic()+120,10)
result=fp.graft_wave(work,wave,jobs,manifest)
fp.write_json(out/'CURRENT_STATE.json',{'models':result,'status':'EXACT_ORIGINAL_ROOT_DEEP_SWEEP_BROAD_CANARY_NOT_YET_MERGED'})
print(json.dumps({'event':'deep_sweep_original_root_accepted',**{k:result[name][k] for k in ('nodes','leaves','open','max_depth')}}),flush=True)
