"""Full optimizer-free replay of V41 components, certificates, and ablations.
This proves the supplied parent certificates, NOT the entire proper-B root.
"""
from pathlib import Path
import json,hashlib,subprocess,sys,tempfile,time,argparse,os
ROOT=Path(__file__).resolve().parent

def file_hashes():
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    for name,digest in manifest['files'].items():
        path=ROOT/name
        if not path.is_file()or hashlib.sha256(path.read_bytes()).hexdigest()!=digest:
            raise ValueError('Static file mismatch: '+name)
    return len(manifest['files'])

def run(jobs=4):
    if not 1<=jobs<=40:raise ValueError('jobs must be 1..40')
    start=time.monotonic();count=file_hashes();results={}
    with tempfile.TemporaryDirectory(prefix='v41_full_replay_')as td:
        env=dict(os.environ);env.update(OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1',V41_JOBS=str(jobs))
        for name in ('verify_input','verify_math','verify_negative','verify_plain_control','verify_cases','verify_ablation'):
            # Explicit absolute script paths avoid inherited same-name modules.
            process=subprocess.run([sys.executable,str(ROOT/(name+'.py'))],cwd=td,env=env,text=True,capture_output=True)
            if process.returncode:raise RuntimeError(name+' failed\n'+process.stdout+process.stderr)
            results[name]=json.loads(process.stdout)
            print(name+': PASS',flush=True)
        process=subprocess.run([sys.executable,str(ROOT/'v41_protocol.py'),str(ROOT/'controls/sample_49_box.json'),str(ROOT/'controls/conditional49_partial.json'),'--allow-open','--cross-check'],cwd=td,env=env,text=True,capture_output=True)
        if process.returncode:raise RuntimeError('conditional control failed\n'+process.stdout+process.stderr)
        results['partial_conditional_control']=json.loads(process.stdout)
    cases=results['verify_cases'];assert cases['complete_parent_boxes']==63 and cases['remaining_sample_boxes']==[49]
    assert cases['BASE_complete']==62 and cases['PIVOT_CYCLE_complete']==1
    assert results['partial_conditional_control']['status']=='OPEN'
    return dict(status='V41_EXACT_DUAL_BOX_AND_63_PARENT_CERTIFICATES_PASS_NOT_GLOBAL_CLOSURE',
       static_files_checked=count,complete_parent_boxes=cases['complete_parent_boxes'],
       contradiction_parent_boxes=cases['contradiction_parents'],alpha_safe_parent_boxes=cases['alpha_safe_parents'],
       remaining_sample_boxes=cases['remaining_sample_boxes'],remaining_reported_original_index=144782,
       BASE_complete=cases['BASE_complete'],PIVOT_CYCLE_complete=cases['PIVOT_CYCLE_complete'],
       checked_bound_certificates=cases['all_intermediate_bounds_replayed'],
       dense_residual_crosschecks=cases['dense_residual_crosschecks'],accepted_contraction_waves=cases['total_waves'],
       matched_ablation=results['verify_ablation'],plain_fixed_point_control=results['verify_plain_control'],mathematics=results['verify_math'],
       input_review=results['verify_input'],negative_tests=results['verify_negative'],
       partial_conditional_control=results['partial_conditional_control'],
       unreceived_round50_full_tree_replayed_here=False,original_ancestry_verified_here=False,
       continuous_splits_added=0,running_local_jobs_modified=False,whole_B_closed=False,macro_ledger='14/15',
       seconds=time.monotonic()-start)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--jobs',type=int,default=4);ap.add_argument('--output')
    a=ap.parse_args();r=run(a.jobs)
    if a.output:Path(a.output).write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(r,ensure_ascii=False,separators=(',',':')))
