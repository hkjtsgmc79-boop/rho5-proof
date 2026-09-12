#!/usr/bin/env python3
"""Complete V31 acceptance. No skip-verification or small-checks-only PASS path."""
from __future__ import annotations
import gzip,hashlib,json,shutil,subprocess,sys,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent


def require(ok,message):
    if not ok:raise RuntimeError(message)


def verify_hashes():
    seen=set()
    for line in (ROOT/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
        digest,name=line.split('  ',1);path=Path(name)
        require(not path.is_absolute() and '..' not in path.parts,'unsafe manifest path')
        require(name not in seen and len(digest)==64,'invalid/duplicate manifest record')
        file=ROOT/path;require(file.is_file(),'missing file '+name)
        require(hashlib.sha256(file.read_bytes()).hexdigest()==digest,'hash mismatch '+name);seen.add(name)
    for name in ('model_source.py','mc_exact_model.json','mc_exact_model.hpp','mc_exact_kernel.hpp','mc_verify.cpp',
                 'small_exact.tree.gz','certificate_manifest.json','proof_statistics.json','verify_model.py',
                 'verify_fraction_replay.py','verify_regressions.py','verify_negative_controls.py'):
        require(name in seen,'critical file not manifested: '+name)
    print('V31_MANIFEST_PASS files='+str(len(seen)),flush=True)


def run(args,cwd=ROOT,timeout=180):
    proc=subprocess.run(args,cwd=cwd,capture_output=True,text=True,timeout=timeout)
    if proc.stdout:print(proc.stdout.rstrip(),flush=True)
    if proc.stderr:print(proc.stderr.rstrip(),file=sys.stderr,flush=True)
    require(proc.returncode==0,'component rejected: '+str(args))
    return proc.stdout


def main():
    started=time.perf_counter();verify_hashes();run([sys.executable,'verify_model.py'])
    certificate=json.loads((ROOT/'certificate_manifest.json').read_text())
    expected=json.loads((ROOT/'proof_statistics.json').read_text())
    require(certificate['target']=='1653/400','wrong target')
    with tempfile.TemporaryDirectory(prefix='rho5_v31_accept_') as td:
        folder=Path(td);tree=folder/'small_exact.tree'
        with gzip.open(ROOT/'small_exact.tree.gz','rb') as source,tree.open('wb') as target:
            shutil.copyfileobj(source,target)
        require(hashlib.sha256(tree.read_bytes()).hexdigest()==certificate['proof_tree_sha256'],'raw tree hash mismatch')
        for name in ('mc_verify.cpp','mc_exact_kernel.hpp','mc_exact_model.hpp'):shutil.copy2(ROOT/name,folder/name)
        binary=folder/'mc_verify'
        run(['g++','-O2','-std=c++17',str(folder/'mc_verify.cpp'),'-o',str(binary)],cwd=folder)
        output=run([str(binary),str(tree)],cwd=folder)
        checked=json.loads(output.strip().splitlines()[-1])
        require(checked['status']=='V31_SMALL_PIVOT_GLOBAL_EXACT_PASS','wrong exact status')
        for key in ('nodes','splits','leaves','open','max_depth','max_support','total_support'):
            require(checked[key]==expected[key],'incorrect coverage statistic '+key)
        require(checked['open']==0,'unpaid frontier')
        run([sys.executable,'verify_fraction_replay.py',str(tree)])
        run([sys.executable,'verify_negative_controls.py',str(binary),str(tree)])
    run([sys.executable,'verify_regressions.py'])
    result=dict(status='V31_SMALL_MOTHER_GLOBAL_BOUND_PASSED',target='1653/400',
                nodes=checked['nodes'],leaves=checked['leaves'],open=0,small_mother='CLOSED',
                k2_high_exit='CLOSED',bilateral_blocked_high_exit='CLOSED',large_mother='OPEN',
                whole_R='OPEN',macro_B22='OPEN',strict_macro_ledger='11/15',
                imported_lemma='rho4_real_CP_equals_4',seconds=time.perf_counter()-started)
    print(json.dumps(result,ensure_ascii=False),flush=True)
if __name__=='__main__':
    try:main()
    except Exception as exc:
        print('V31_REJECTED: '+str(exc),file=sys.stderr)
        sys.exit(1)
