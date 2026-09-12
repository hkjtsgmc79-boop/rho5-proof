#!/usr/bin/env python3
"""V36 received-component review and NEW proof/certificate replay.

Does not replay missing Round47, high-r or prior upper-range original-root trees.
Their complete local verification is an explicitly adopted mathematical input.
All working output and fresh compilation occur in a new temporary directory.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    if not __debug__:
        raise RuntimeError('Verification must not be run with Python -O')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--result',type=Path,help='Optional path for the final receipt')
    args=parser.parse_args();start=time.monotonic()
    manifest=json.loads((ROOT/'MANIFEST.json').read_text(encoding='utf-8'))
    for name,h in manifest['files'].items():
        p=ROOT/name
        if not p.is_file() or digest(p)!=h:raise ValueError('static manifest mismatch: '+name)
    print(f'V36 static files verified: {len(manifest["files"])}',flush=True)
    with tempfile.TemporaryDirectory(prefix='rho5_v36_replay_') as temp:
        W=Path(temp)/'source';W.mkdir()
        for name in manifest['files']:
            dest=W/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/name,dest)
        (W/'evidence').mkdir(exist_ok=True)
        env=os.environ.copy();env.update(PYTHONOPTIMIZE='0',OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
        commands=[
            ('received_light','audit_round47.py'),
            ('inherited_local_dictionary','inputs/round47/source/verify_v35_components.py'),
            ('received_H_rule','inputs/round47/source/verify_weighted_height.py'),
            ('received_A_rules','inputs/round47/source/verify_alpha_ports.py'),
            ('assembly','verify_assembly.py'),
            ('two_gap_certificate','verify_two_gap_certificate.py'),
            ('proper_B_controls','verify_gap_witnesses.py'),
            ('new_B_dictionaries','verify_new_components.py'),
        ]
        summaries={}
        for label,script in commands:
            t=time.monotonic();print(f'\n>>> {label}: {script}',flush=True)
            p=subprocess.run([sys.executable,str(W/script)],cwd=W,capture_output=True,text=True,env=env,timeout=240)
            print(p.stdout,flush=True)
            if p.stderr:print(p.stderr,file=sys.stderr,flush=True)
            if p.returncode!=0:raise RuntimeError(f'{label} returned {p.returncode}')
            (W/'evidence'/f'replayed_{label}.log').write_text(p.stdout+p.stderr,encoding='utf-8')
            summaries[label]={'returncode':0,'seconds':time.monotonic()-t}
        # Rebuild, rather than trusting pre-generated task/certificate identity.
        for script,targets in [('build_two_gap_certificate.py',['two_gap_certificate.json']),
                               ('build_b_models.py',['next_B_models/base_model.json','next_B_models/contacts54.json','next_B_models/representatives36.json'])]:
            old={t:digest(W/t) for t in targets}
            p=subprocess.run([sys.executable,str(W/script)],cwd=W,capture_output=True,text=True,env=env,timeout=30)
            if p.returncode:raise RuntimeError(p.stderr)
            for t,h in old.items():
                if digest(W/t)!=h:raise ValueError('regenerated identity differs: '+t)
        light=json.loads((W/'evidence/round47_review.json').read_text())
        assembly=json.loads((W/'evidence/assembly_verification.json').read_text())
        cert=json.loads((W/'evidence/two_gap_verification.json').read_text())
        new=json.loads((W/'evidence/new_components.json').read_text())
        result={
            'status':'V36_RST_ASSEMBLY_AND_PROPER_B_LOCAL_BRIDGES_PASS',
            'received_static_files_checked':light['received_files_hashed'],
            'unreceived_global_trees_replayed_here':False,
            'adopted_round47_local_receipt_totals':light['totals'],
            'complete_X':'assembled from explicit adopted frozen complete-scope inputs',
            'R_ST':'actual-matrix assembly proved under those inputs',
            'controller_ledger_before_registration':'11/15',
            'controller_ledger_registration_proposal':'14/15',
            'new_proper_B_flow_certificates':len(cert['cases']),
            'new_B_flow_source_dimension':24,'new_B_jacobian_dimension':23,
            'B_original_contact_classes':54,'B_transpose_task_representatives':36,
            'B_global_proof_tree_supplied':False,'whole_B':'OPEN',
            'new_symbolic_assembly_assertions':assembly['symbolic_zero_assertions'],
            'new_B_symbolic_assertions':new['exact_symbolic_zero_assertions'],
            'modules':summaries,'seconds':time.monotonic()-start,
        }
        if args.result:
            args.result.parent.mkdir(parents=True,exist_ok=True)
            args.result.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
        print(json.dumps(result,ensure_ascii=False),flush=True)
    return 0

if __name__=='__main__':
    try:sys.exit(main())
    except Exception as exc:
        print(f'V36_REPLAY_FAILED: {type(exc).__name__}: {exc}',file=sys.stderr)
        sys.exit(1)
