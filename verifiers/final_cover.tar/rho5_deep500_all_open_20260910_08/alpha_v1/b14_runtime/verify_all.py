#!/usr/bin/env python3
"""Rebuild only 8 selected original paths, then apply independent alpha ports.
No optimizer, no new split, no source-tree mutation, no full-root claim.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
 manifest=json.loads((ROOT/'MANIFEST_SHA256.json').read_text())
 for n,h in manifest['files'].items():
  p=ROOT/n
  if not p.is_file()or sha(p)!=h:raise ValueError('Package byte identity mismatch: '+n)
 runs=[('rebuild_starters.py',['SOURCE_REBUILD.json']),('diagnose.py',['DIAGNOSTIC.json']),('diagnose_v43.py',['V43_APPLICATION.json']),('applicability.py',['APPLICABILITY.json']),('matrix_audit.py',['WITNESS_MEMBERSHIP.json']),('audit_source_witness.py',['WITNESS_PATH_AUDIT.json']),('audit_transport.py',['TRANSPORT_AUDIT.json']),('verify_port_controls.py',['ALPHA_PROPOSALS.json','ALPHA_ACCEPTANCE.json']),('literal_port_check.py',['LITERAL_PORT_CHECK.json'])]
 results=[];start=time.monotonic()
 for script,names in runs:
  t=time.monotonic();cmd=[sys.executable]+(['-O']if sys.flags.optimize else[])+['-S',str(ROOT/script)]
  pr=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True)
  if pr.returncode:raise RuntimeError(script+' failed\n'+pr.stdout+'\n'+pr.stderr)
  for name in names:
   if(ROOT/name).read_bytes()!=(ROOT/'expected'/name).read_bytes():raise ValueError('Rebuilt evidence differs: '+name)
  results.append({'script':script,'status':'PASS','outputs':{n:sha(ROOT/n)for n in names},'seconds':time.monotonic()-t})
  print(script,'PASS',flush=True)
 receipt={'status':'B14_SEVEN_SOURCE_BOUND_ALPHA_PROOFS_AND_ONE_EXACT_GAMMA_WITNESS_PASS','results':results,'seconds':time.monotonic()-start,'ordinary_or_optimized':sys.flags.optimize,'frozen_theorem_dependencies_consumed_not_reproved':True,'full_root_replayed':False,'unvisited_sibling_math_replayed':False,'production_tree_modified':False}
 (ROOT/'REPLAY_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(receipt['status'])
if __name__=='__main__':
 try:main()
 except Exception as e:print('REJECTED:',e,file=sys.stderr);raise SystemExit(2)
