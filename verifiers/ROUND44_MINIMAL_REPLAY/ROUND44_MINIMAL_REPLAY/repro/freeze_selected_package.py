"""Freeze an explicit selection of completed new proofs; run on X.

Config: {sources:{id:{directory,tree,verify_log}},claims:[{kind,K,J}],target}.
This collector does not accept a theorem: repro/replay_new.py does that next.
"""
from pathlib import Path
import argparse,hashlib,json,shutil

def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        while b:=f.read(1024*1024):h.update(b)
    return h.hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('config',type=Path)
    ap.add_argument('output',type=Path);ap.add_argument('--code-dir',type=Path,required=True)
    ap.add_argument('--controls-dir',type=Path,required=True)
    a=ap.parse_args();root=Path.cwd().resolve();cfg=json.loads(a.config.read_text())
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
    code=a.code_dir.resolve();repro=out/'repro';repro.mkdir()
    for path in sorted(code.rglob('*')):
        if path.is_file() and '__pycache__' not in path.parts and path.suffix in ('.py','.md','.json','.cpp','.hpp'):
            destination=repro/path.relative_to(code)
            destination.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(path,destination)
    selected=[];origins={}
    for label,spec in cfg['sources'].items():
        source=(root/spec['directory']).resolve()
        if root not in source.parents:raise ValueError('Proof source must be inside this task directory.')
        verification=json.loads((source/spec['verify_log']).read_text())
        if verification.get('status')!='R44_MIDBAND_INTERVAL_EXACT_PASS' or verification.get('open')!=0:
            raise ValueError('An incomplete or rejected discovery cannot be selected: '+label)
        destination=out/'proofs'/label;destination.mkdir(parents=True)
        files={'model.json':'model.json','mc_exact_model.hpp':'mc_exact_model.hpp',
               'mc_exact_kernel.hpp':'mc_exact_kernel.hpp','mc_verify.cpp':'mc_verify.cpp',
               spec['tree']:'result.tree'}
        for old,new in files.items():shutil.copyfile(source/old,destination/new)
        history=out/'source_records'/label;history.mkdir(parents=True)
        shutil.copyfile(source/spec['verify_log'],history/'original_verify.log')
        for name in ('discovery.log','resume_discovery.log'):
            if (source/name).is_file():shutil.copyfile(source/name,history/name)
        origins[label]={'task_directory':spec['directory'],'tree_source':spec['tree'],
                        'verification':verification,
                        'input_sha256':{name:digest(destination/name) for name in files.values()}}
        selected.append(label)
    selection={'schema':'rho5.cqg.round44.proof-selection.v1','target':cfg.get('target','4132517/1000000'),
               'proof_ids':selected,'claims':cfg['claims']}
    (out/'SELECTION.json').write_text(json.dumps(selection,indent=2)+'\n')
    (out/'SOURCE_RECORDS.json').write_text(json.dumps(origins,indent=2)+'\n')
    controls=out/'inputs'/'controls';controls.mkdir(parents=True)
    for name in ('exact_core_block_witness.json','exact_nearpeak_nowall.json'):
        shutil.copyfile(a.controls_dir/name,controls/name)
    audits=out/'saved_audits';audits.mkdir()
    for name in ('ROOTS_EXACT_AUDIT.json','RECTANGLES_EXACT_AUDIT.json','LIFT_EXACT_AUDIT.json',
                 'HEAD_ANCHOR_EXACT_AUDIT.json','R44_ACTUAL_MATRIX_REGRESSION.json'):
        if (root/name).is_file():shutil.copyfile(root/name,audits/name)
    print(json.dumps({'status':'EXPLICIT_NEW_SELECTION_FROZEN_PENDING_COLD_REPLAY',
                      'directory':str(out),'proofs':selected,'claims':cfg['claims']}))

if __name__=='__main__':main()
