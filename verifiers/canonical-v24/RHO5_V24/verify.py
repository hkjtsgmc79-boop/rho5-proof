"""V24 default read-only acceptance; no LP solver is needed.

Use --full-chain to rerun V22 -> V21 -> GO V20 -> old dependencies as well.
The default replays the new six proofs, algebra, regression tests, and V23's
unchanged algebra acceptance.  All numerical optimization is generation-only.
"""
from __future__ import annotations
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,os,shutil,subprocess,sys,tempfile,time,zipfile
ROOT=Path(__file__).resolve().parent
KEYS=['PX1','PX2','PY1','PY2','EX1','EX2']
BASE='RHO5_V23_Least_Optimal_E_and_Eleven_Middle_Budgets_2026-09-06_Algebra_Verification.zip'
BASE_SHA='28333ee98e804f39998689b242a2880909be39aaa7bcb26e77e75186dc73459b'

def check_hashes():
    for line in (ROOT/'SHA256SUMS.txt').read_text().splitlines():
        if not line.strip():continue
        he,name=line.split('  ',1);p=ROOT/name
        assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==he,'file hash: '+name
    assert hashlib.sha256((ROOT/'dependencies'/BASE).read_bytes()).hexdigest()==BASE_SHA
    print('PASS file hashes and frozen V23 archive',flush=True)

def rebuild_models():
    import model_spec
    degrees=[]
    with tempfile.TemporaryDirectory() as tmp:
        for key in KEYS:
            sp=model_spec.spec(key[1],key[2],key[0]);saved=json.loads((ROOT/'certificates'/f'{key}.json').read_text())
            assert sp==saved,'polynomial/gradient model mismatch '+key
            hp=Path(tmp)/f'{key}.hpp';model_spec.write_cpp(sp,hp)
            assert hp.read_bytes()==(ROOT/'cpp'/f'{key}.hpp').read_bytes(),'graph header mismatch '+key
            vs,eq,ins=model_spec.system(key[1],key[2],key[0]);import sympy as s
            degrees.append(max(s.Poly(e,*vs).total_degree()for _,e in eq+ins))
    assert max(degrees)==6
    print('PASS six exact systems, all symbolic derivatives and computational graphs; max polynomial degree 6',flush=True)

def compile_one(key):
    subprocess.run(['g++','-std=c++17','-O2','-fPIC','-shared','-I'+str(ROOT/'cpp'),f'-DMODEL_HEADER="{key}.hpp"',str(ROOT/'cpp/linearize.cpp'),'-o',str(ROOT/f'linear_{key}.so')],check=True)
    return key

def replay_one(key):
    import verify_lp
    return verify_lp.replay(key,verbose=False)

def regression():
    import canonical_target as new
    sys.path.insert(0,str(ROOT/'support'));import target_point as old
    from four_capacities import serial
    head=json.load(open(ROOT/'support/source_v9_witness.json'))['theta']
    results=[]
    for f in ['1653/400','206625837/50000000','4132517/1000000','2066259/500000']:
        a=new.decide(head,f);b=old.wall_decide(head,f)
        assert (a['status']=='HEAD_SAT')==(b['status']=='WALL_SAT'),'target compatibility'
        results.append(dict(target=f,status=a['status'],F=str(a.get('F','')),reason=a.get('reason')))
    try:new.decide(head,4.132517)
    except TypeError:pass
    else:raise AssertionError('floating target accepted')
    print('PASS four existing-head target compatibility tests; two full exact wall matrices; float rejection',flush=True)
    return results

def negative_controls():
    import verify_lp
    attempts={'fake_leaf':'L\nEND\n','fake_dual':'F 1 0 1\nEND\n','truncated':'B 0 3000000000\n'}
    rejected=[]
    with tempfile.TemporaryDirectory() as td:
        for label,text in attempts.items():
            p=Path(td)/(label+'.proof');p.write_text('V24-EXACT-MEAN-FARKAS-1 32\n'+text)
            try:verify_lp.replay('PX1',p,False)
            except (AssertionError,ValueError,IndexError):rejected.append(label)
            else:raise AssertionError('false proof accepted: '+label)
    print('PASS false interval leaf, false dual multiplier and truncated-tree rejection',flush=True)
    return rejected

def source_replay(full=False):
    with tempfile.TemporaryDirectory(prefix='rho5_v24_source_') as td:
        with zipfile.ZipFile(ROOT/'dependencies'/BASE)as z:z.extractall(td)
        d=Path(td)/'RHO5_V23_Analytic'
        subprocess.run([sys.executable,'verify.py'],cwd=d,check=True)
        if full:
            dep=next((d/'dependencies').glob('*.zip'));p=Path(td)/'V22'
            with zipfile.ZipFile(dep)as z:z.extractall(p)
            dd=next(x for x in p.iterdir()if x.is_dir())
            subprocess.run([sys.executable,'verify.py','--engine','cpp','--jobs','4'],cwd=dd,check=True)
    print('PASS unchanged source replay'+(' and complete V22 legacy chain'if full else ' (V23 algebra)'),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--jobs',type=int,default=4);ap.add_argument('--full-chain',action='store_true');ap.add_argument('--skip-hashes',action='store_true',help='development only');args=ap.parse_args()
    start=time.time()
    if not args.skip_hashes:check_hashes()
    rebuild_models()
    import proof_identities
    identities=proof_identities.run();assert len(identities)==33
    print('PASS 33 exact algebra identities and rational root-bound comparisons',flush=True)
    if not shutil.which('g++'):raise RuntimeError('A C++17 compiler is required by this acceptance package')
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs)as ex:list(ex.map(compile_one,KEYS))
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.jobs)as ex:reports=list(ex.map(replay_one,KEYS))
    expected=json.loads((ROOT/'certificate_statistics.json').read_text())
    for got in reports:
        old=next(x for x in expected['systems']if x['key']==got['key'])
        for name in ['nodes','leaves','interval_leaves','farkas_leaves','max_depth']:assert got[name]==old[name]
        print('PASS',got['key'],{k:got[k]for k in ['nodes','leaves','farkas_leaves','max_depth']},flush=True)
    total={k:sum(a[k]for a in reports)for k in ['nodes','leaves','interval_leaves','farkas_leaves']}
    assert total==expected['total'] and expected['open_leaves']==0
    reg=regression();neg=negative_controls();source_replay(args.full_chain)
    print('V24 EXACT ACCEPTANCE PASS',json.dumps(total),flush=True)
    print('VERDICT: exceptional representative contacts excluded for F >= 1653/400. Canonical E=L_D, unique K24, five middle budgets in this layer.',flush=True)
    print('FINAL alpha WALL THEOREM: NOT PROVED. MACRO LEDGER: 11/15.',flush=True)
    print('Elapsed seconds:',time.time()-start,flush=True)
