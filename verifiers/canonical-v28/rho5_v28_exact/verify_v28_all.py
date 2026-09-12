#!/usr/bin/env python3
"""Mandatory full acceptance: no partial mode and no numerical optimizer."""
from pathlib import Path
import hashlib,subprocess,sys,json,time
BASE=Path(__file__).resolve().parent
if sys.flags.optimize:raise RuntimeError('Run without -O: inherited verifiers use assertions.')
manifest=BASE/'SHA256SUMS.txt'
if not manifest.exists():raise FileNotFoundError('Missing mandatory SHA256SUMS.txt')
for ln in manifest.read_text().splitlines():
    if not ln.strip():continue
    digest,rel=ln.split('  ',1);p=(BASE/rel).resolve()
    if not p.is_relative_to(BASE):raise RuntimeError('invalid manifest path')
    if hashlib.sha256(p.read_bytes()).hexdigest()!=digest:raise RuntimeError('Hash mismatch '+rel)
print('V28_HASH_MANIFEST_PASS',flush=True)
checks=[
 ('verify_v28_symbolic_bridge.py',BASE),
 ('verify_v28_kernel.py',BASE),
 ('verify_v28_coverage.py',BASE),
 ('verify_v28_negative_controls.py',BASE),
 ('verify_v28_bridges.py',BASE),
 ('verify_jacobian_recovered.py',BASE/'RHO5_V26_REBUILT'),
 ('verify_upper_tree_recovered.py',BASE/'RHO5_V26_REBUILT'),
 ('verify_v28_carrier.py',BASE),
 ('verify_alpha_interval.py',BASE),
 ('verify_resultant.py',BASE/'RHO5_V26_REBUILT'),
 ('verify_p61_root.py',BASE/'RHO5_V26_REBUILT')]
started=time.time();runs=[]
for script,folder in checks:
    print('==>',script,flush=True);t=time.time()
    subprocess.run([sys.executable,str(folder/script)],cwd=folder,check=True)
    runs.append({'script':script,'seconds':time.time()-t})
coverage=json.loads((BASE/'coverage_verification.json').read_text())
if coverage['status']!='V28_FULL_GLOBAL_LOCALIZATION_EXACT_PASS' or not coverage['global_coverage'] or coverage['open_grafts']:
    raise RuntimeError('Full localization not certified')
output={'status':'V28_COMPLETE_CANONICAL_BOUND_CERTIFICATES_PASS','assumed_inputs':'Frozen V24/T24, V25 equivalence, and stated high-value lemmas; see REPORT.md',
        'full_global_localization':True,'open_frontiers':0,'runs':runs,'seconds':time.time()-started,
        'whole_R_closed':False,'macro_ledger':'11/15'}
(BASE/'v28_full_verification.json').write_text(json.dumps(output,indent=2))
print(output['status'],flush=True)
