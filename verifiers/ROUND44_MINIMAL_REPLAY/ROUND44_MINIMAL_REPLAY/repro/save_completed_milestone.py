"""Preserve only already verified new certificates before further research."""
from pathlib import Path
import hashlib,json,zipfile

root=Path.cwd()
chosen={'full218_I':'k218_I_G','full218_II':'k218_II_G',
        'high210_I':'k210_I_highG','high210_II':'k210_II_highG'}
manifest={'status':'FOUR_COMPLETED_NEW_CERTIFICATES_NOT_FINAL_PACKAGE','files':[], 'certificates':{}}
output=root/'ROUND44_COMPLETED_MILESTONE_218.zip'
if output.exists():raise RuntimeError('Use the existing immutable milestone archive.')
with zipfile.ZipFile(output,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=2) as z:
    for label,directory in chosen.items():
        source=root/directory
        result=json.loads((source/'resumed_verify.log').read_text())
        assert result['status']=='R44_MIDBAND_INTERVAL_EXACT_PASS' and result['open']==0
        manifest['certificates'][label]=result
        for name in ['model.json','mc_exact_model.hpp','mc_exact_kernel.hpp','mc_verify.cpp',
                     'resumed.tree','resumed_verify.log','discovery.log','resume_discovery.log']:
            path=source/name
            archive=f'proofs/{label}/'+('result.tree' if name=='resumed.tree' else name)
            digest=hashlib.sha256()
            with path.open('rb') as f:
                while block:=f.read(1024*1024):digest.update(block)
            manifest['files'].append({'path':archive,'sha256':digest.hexdigest(),'bytes':path.stat().st_size})
            z.write(path,archive)
    for name in ['K218_MODEL_AUDIT.json','K210_HIGH_MODEL_AUDIT.json','HEAD_ANCHOR_EXACT_AUDIT.json',
                 'ROOTS_EXACT_AUDIT.json','RECTANGLES_EXACT_AUDIT.json','LIFT_EXACT_AUDIT.json',
                 'R44_ACTUAL_MATRIX_REGRESSION.json']:
        z.write(root/name,'audits/'+name)
    z.writestr('MANIFEST.json',json.dumps(manifest,indent=2)+'\n')
digest=hashlib.sha256(output.read_bytes()).hexdigest()
receipt={'path':output.name,'bytes':output.stat().st_size,'sha256':digest,
         'nodes':sum(r['nodes'] for r in manifest['certificates'].values()),
         'leaves':sum(r['leaves'] for r in manifest['certificates'].values()),'open':0}
(root/'ROUND44_COMPLETED_MILESTONE_218_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
