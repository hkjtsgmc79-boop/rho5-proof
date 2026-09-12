"""P01: single guarded Lean with bounded dependency snapshots before and after each invocation."""
from pathlib import Path
import os,sys,subprocess,json,hashlib,shutil,time,fcntl,re
R=Path('/root/microscope_ws/rho5_codex_c02_assembly_20260912/p01')
P=Path('/root/microscope_ws/rho5_lean_pilot_20260911');PKG=P/'project/.lake/packages';LEAN=P/'runtime/lean-4.30.0-linux/bin/lean'
roots=[R/'build',Path('/root/microscope_ws/rho5_lean_dsh_20260911/D141/cache/lean')]
roots += [PKG/n/'.lake/build/lib/lean' for n in ['batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible']]
os.environ.update(LEAN_PATH=':'.join(map(str,roots)),OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1',D135_AS_LIMIT=str(12*1024**3))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
locks=json.loads((R/'inputs/FINITE_UPSTREAM_LOCK.json').read_text())+json.loads((R/'inputs/CURRENT_BRIDGE_LOCK.json').read_text());idx={d['module']:d for d in locks}
lock=(R/'results/compile.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
def resolve(m):
 rel=Path(m.replace('.','/')).with_suffix('.olean')
 return next(p/rel for p in roots if (p/rel).is_file())
def snapshot(deps):
 out=[]
 for m in sorted(set(deps)|set(idx)):
  p=resolve(m);src=R/'src'/Path(m.replace('.','/')).with_suffix('.lean') if m.startswith('Rho5.PhaseOne') else Path(idx[m]['source'])
  h,o=sha(src),sha(p)
  if m in idx:assert (h,o)==(idx[m]['source_sha256'],idx[m]['olean_sha256']),m
  out.append(dict(module=m,source=str(src),source_sha256=h,olean=str(p),olean_sha256=o))
 return out
version=subprocess.check_output([str(LEAN),'--version'],text=True).strip()
for module in sys.argv[1:]:
 leans=[l for l in subprocess.check_output(['ps','-eo','pid,ppid,ni,rss,comm'],text=True).splitlines() if l.split()[-1] in ('lean','lean4')]
 mem=int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:')));free=shutil.disk_usage(R).free
 print(json.dumps({'lean_jobs':leans,'available_mem_kib':mem,'free_disk_bytes':free}),flush=True)
 if len(leans)>=6 or mem<16*1024**2 or free<10*1024**3:raise SystemExit('DEFER: shared resource guard')
 src=R/'src'/Path(module.replace('.','/')).with_suffix('.lean');out=R/'build'/Path(module.replace('.','/')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 src_hash=sha(src);deps=re.findall(r'^import\s+(\S+)',src.read_text(),re.M);before=snapshot(deps)
 stem=module+'_'+str(time.time_ns());log=R/'results'/(stem+'.log');pre=R/'results'/(stem+'.before.json')
 pre.write_text(json.dumps({'module':module,'source_sha256':src_hash,'created_ns':time.time_ns(),'direct_imports':deps,'finite_dependency_snapshot':before,'lean_version':version,'LEAN_PATH':os.environ['LEAN_PATH']},indent=2)+'\n')
 cmd=['nice','-n','10','python3',str(R/'tools/guard.py'),'180','-j1','-M8192','-R',str(R/'src'),'-o',str(out),str(src)]
 start=time.time()
 with log.open('w') as f:p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,cwd=R/'src')
 elapsed=time.time()-start;after=snapshot(deps)
 rec=dict(module=module,exit_code=p.returncode,wall_seconds=elapsed,source_sha256=src_hash,source_sha256_after=sha(src),olean_sha256=sha(out) if p.returncode==0 else None,source_bytes=src.stat().st_size,olean_bytes=out.stat().st_size if p.returncode==0 else None,log=str(log),log_sha256=sha(log),command=cmd,LEAN_PATH=os.environ['LEAN_PATH'],lean_version=version,before_snapshot=str(pre),before_snapshot_sha256=sha(pre),direct_imports=deps,dependency_snapshot_before=before,dependency_snapshot_after=after,dependencies_unchanged=before==after,source_unchanged=sha(src)==src_hash,preflight_lean_jobs=leans,available_mem_kib=mem,free_disk_bytes=free)
 (R/'results'/(stem+'.json')).write_text(json.dumps(rec,indent=2)+'\n')
 if p.returncode:print(log.read_text(),flush=True)
 else:print(json.dumps({k:rec[k] for k in ['module','exit_code','wall_seconds','source_sha256','olean_sha256','dependencies_unchanged','source_unchanged','log']}),flush=True)
 if p.returncode:raise SystemExit(p.returncode)
 if before!=after or sha(src)!=src_hash:raise SystemExit('changed source/dependencies: do not accept this object')
