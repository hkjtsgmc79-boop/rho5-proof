from pathlib import Path
import os,json,hashlib
R=Path('/root/microscope_ws/rho5_codex_c02_assembly_20260912/p01')
C=R.parent/'rebuild_01/build';D=Path('/root/microscope_ws/rho5_lean_dsh_20260911/D84');CACHE=Path('/root/microscope_ws/rho5_lean_dsh_20260911/D141/cache/lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for n in ['build/Rho5/PhaseOne','results']:(R/n).mkdir(parents=True,exist_ok=True)
links=[]
for p in (C/'Rho5').iterdir():
 q=R/'build/Rho5'/p.name
 if not q.exists():q.symlink_to(p,target_is_directory=p.is_dir());links.append({'view':str(q),'target':str(p)})
p=D/'lane_root/Rho5/ExternalV43Existence';q=R/'build/Rho5/ExternalV43Existence'
if not q.exists():q.symlink_to(p,target_is_directory=True);links.append({'view':str(q),'target':str(p)})
# Reuse D84's already assembled third-party ODE view. The Rho5 namespace
# remains the canonical C02 rebound view above; no third-party closure scan.
q=R/'build/Mathlib'
if q.exists() and (not q.is_symlink() or q.resolve() != D/'iso_root/Mathlib'):
 old=R/'mathlib_environment_attempts';old.mkdir(exist_ok=True)
 q.rename(old/'initial_C02_plus_finite_ODE_grafts')
if not q.exists():q.symlink_to(D/'iso_root/Mathlib',target_is_directory=True)
need=[];grafts=[]
locks=json.loads((R/'inputs/FINITE_UPSTREAM_LOCK.json').read_text())
for d in locks:
 assert sha(d['source'])==d['source_sha256'],d['module']+' source'
 assert sha(d['olean'])==d['olean_sha256'],d['module']+' object'
 p=R/'build'/Path(d['module'].replace('.','/')).with_suffix('.olean')
 assert sha(p)==d['olean_sha256'],d['module']+' resolved'
extra=[]
for m,src,obj in [
 ('Rho5.LocalAnalysis.Pilot','/root/microscope_ws/rho5_lean_pilot_20260911/project/Rho5/LocalAnalysis/Pilot.lean',str(C/'Rho5/LocalAnalysis/Pilot.olean')),
 ('Mathlib.Analysis.ODE.PicardLindelof','/root/microscope_ws/rho5_lean_pilot_20260911/project/.lake/packages/mathlib/Mathlib/Analysis/ODE/PicardLindelof.lean',str(D/'iso_root/Mathlib/Analysis/ODE/PicardLindelof.olean'))]:
 extra.append(dict(module=m,source=src,source_sha256=sha(src),olean=obj,olean_sha256=sha(obj),evidence='P01 current finite bridge fingerprint; upstream evidence inherited'))
(R/'inputs/CURRENT_BRIDGE_LOCK.json').write_text(json.dumps(extra,indent=2)+'\n')
(R/'results/VIEW_SETUP.json').write_text(json.dumps({'canonical_Rho5':str(C),'top_level_links':links,'mathlib_view':str(D/'iso_root/Mathlib'),'method':'Reuse accepted D84 Mathlib view; retain C02 canonical Rho5 namespace','full_closure_scan':False,'upstream_rebuilds':0},indent=2)+'\n')
print(json.dumps({'finite_upstream_locks':len(locks),'bridge_locks':len(extra),'mathlib_grafted_files':len(grafts),'mathlib_grafted_modules':len(set(d['module'] for d in grafts))}))
