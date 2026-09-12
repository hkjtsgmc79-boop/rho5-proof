#!/usr/bin/env python3
"""Recheck hashes, then run exact V27 tests in an isolated temporary folder."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

root=Path(__file__).resolve().parent
manifest=json.loads((root/'MANIFEST.json').read_text())
for name,digest in manifest['sha256'].items():
    path=root/name
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=digest:
        raise SystemExit('Hash mismatch: '+name)
print('Package hashes: PASS')
programs=('verify_symbolic.py','run_regressions.py','verify_entry_budgets.py')
with tempfile.TemporaryDirectory(prefix='rho5_v27_verify_') as tmp:
    work=Path(tmp)
    for name in ('v27_exact.py',*programs):
        shutil.copy2(root/name,work/name)
    for name in programs:
        proc=subprocess.run([sys.executable,name],cwd=work,text=True,
                            stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
        print(proc.stdout,end='')
        if proc.returncode:
            raise SystemExit('Verification failed: '+name)
    outputs={name:json.loads((work/name).read_text()) for name in
             ('symbolic_results.json','regression_results.json','entry_budget_results.json')}
    if any(out['status']!='PASS' for out in outputs.values()):
        raise SystemExit('Missing PASS status')
print('V27 exact replay: PASS')
print('Scope: identities, explicit physical witnesses and analytic-entry dictionaries;')
print('NOT a certificate excluding the remaining whole-R high-value sign domains.')
