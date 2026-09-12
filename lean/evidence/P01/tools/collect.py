from pathlib import Path
import json,re,hashlib,shutil,tarfile,time
R=Path('/root/microscope_ws/rho5_codex_c02_assembly_20260912/p01');E=R/'evidence'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for n in ['src','tools','inputs','results']:
 shutil.copytree(R/n,E/n,dirs_exist_ok=True)
selected=[];attempts=[]
for p in sorted((R/'results').glob('Rho5.*.json')):
 if p.name.endswith('.before.json'):continue
 d=json.loads(p.read_text());d['receipt_file']=p.name;attempts.append(d)
for m in ['Rho5.PhaseOne','Rho5.PhaseOne.Audit']:
 rel=Path(m.replace('.','/'));src=(R/'src'/rel).with_suffix('.lean');obj=(R/'build'/rel).with_suffix('.olean')
 ds=[d for d in attempts if d['module']==m and d['exit_code']==0 and d['source_sha256']==sha(src)]
 assert len(ds)==1,(m,len(ds));d=ds[0]
 assert d['olean_sha256']==sha(obj) and d['dependencies_unchanged'] and d['source_unchanged']
 assert d['log_sha256']==sha(d['log']) and d['before_snapshot_sha256']==sha(d['before_snapshot'])
 for dep in d['dependency_snapshot_after']:
  assert dep['source_sha256']==sha(dep['source']) and dep['olean_sha256']==sha(dep['olean']),dep['module']
 dest=(E/'compiled'/rel).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(obj,dest)
 selected.append(d)
audit=Path(selected[1]['log']).read_text()
raw=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit,re.S)
records=[{'canonical_target':n,'axioms':[re.sub(r'\.\{[^}]*\}','',a.strip()) for a in axs.split(',') if a.strip()]} for n,axs in raw]
assert len(records)==33,len(records)
assert all(set(d['axioms'])<=set(['propext','Classical.choice','Quot.sound']) for d in records)
loaded=re.findall(r'^P01_LOADED_MODULE (\S+)',audit,re.M);assert len(loaded)==len(set(loaded))
assert 'Rho5.PhaseOne.Audit' not in loaded and 'Rho5.PhaseOne.Examples' not in loaded
banned=[m for m in loaded if re.search(r'V31|MainlineTree|BatchKernel|BatchScaleG03|CertificateContraction',m)]
assert not banned,banned
(E/'FINAL_THEOREM_TYPES.txt').write_text(audit.split('P01_LOADED_MODULE')[0])
(E/'AXIOMS.json').write_text(json.dumps({'status':'PASS','targets_checked':len(records),'records':records,'public_aliases':json.loads((R/'inputs/PUBLIC_TARGETS.json').read_text()),'note':'Lean export names resolve to the original declarations; no duplicate proof declarations are introduced.'},indent=2)+'\n')
(E/'ACTUAL_IMPORTS.json').write_text(json.dumps({'modules':loaded,'Rho5_count':len(loaded),'default_roots':['Rho5.Integration.StagedAssembly.Conditional','Rho5.ExternalV43Existence.PhysicalTrip'],'phase_two_matches':banned,'new_audit_or_examples_imported':False},indent=2)+'\n')
metrics=[]
for d in selected:
 text=Path(d['log']).read_text();metrics.append({k:float(re.search('^'+k+r': ([0-9.]+)',text,re.M).group(1)) for k in ['wall_seconds','child_user_cpu_seconds','child_sys_cpu_seconds','peak_rss_kib','child_vmpeak_kib']})
status={'status':'PRODUCT_AND_AUDIT_PASS_AWAITING_DSH_PACKAGE_INPUTS','selected':selected,'attempts':[{k:d[k] for k in ['module','exit_code','wall_seconds','source_sha256','log','log_sha256','receipt_file']} for d in attempts],'selected_wall_seconds':sum(d['wall_seconds'] for d in selected),'failed_attempt_wall_seconds':sum(d['wall_seconds'] for d in attempts if d['exit_code']),'attempt_count':len(attempts),'failure_count':sum(d['exit_code']!=0 for d in attempts),'metrics':metrics,'public_target_count':len(records),'actual_Rho5_import_count':len(loaded),'inherited_upstream_evidence':['C02 rebound ACCEPTED_SCOPED','D84 ACCEPTED_DECLARED_SCOPE'],'cold_build_performed':False,'upstream_rebuilds':0,'tree_computations':0,'resource_limits':{'owner_Lean':1,'global_Lean':6,'threads':1,'rss_GiB':8,'AS_GiB':12,'timeout_seconds':180},'environment_note':'Canonical C02 Rho5 objects plus D84 ExternalV43Existence; accepted D84 third-party Mathlib view. Initial C02 third-party view lacked ODE imports.'}
(E/'BUILD_STATUS.json').write_text(json.dumps(status,indent=2)+'\n')
archive=R/'p01_thin_evidence.tar.gz'
with tarfile.open(archive,'w:gz') as tf:
 for p in sorted(E.rglob('*')):
  if p.is_file():tf.add(p,arcname=str(p.relative_to(E)))
print(json.dumps({'archive':str(archive),'sha256':sha(archive),'bytes':archive.stat().st_size,'selected_seconds':status['selected_wall_seconds'],'failures':status['failure_count'],'Rho5_imports':len(loaded),'targets':len(records)},indent=2))
