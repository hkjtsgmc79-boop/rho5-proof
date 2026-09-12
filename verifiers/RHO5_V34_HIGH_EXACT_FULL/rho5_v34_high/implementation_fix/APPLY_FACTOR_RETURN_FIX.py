"""Create a new fixed V34 copy; keep the original archive untouched.
Usage: python APPLY_FACTOR_RETURN_FIX.py rho5_v34_exact.zip NEW_OUTPUT_DIRECTORY
Then enter NEW_OUTPUT_DIRECTORY/rho5_v34_exact and run python verify_all.py.
"""
from pathlib import Path
import sys, zipfile, hashlib, json

def digest(data):
    return hashlib.sha256(data).hexdigest()

def main():
    archive=Path(sys.argv[1]).resolve();out=Path(sys.argv[2]).resolve()
    expected='786182ae81d5c6b8353e321869a28151ee692dcb884675812c50f3ddac6cc360'
    if digest(archive.read_bytes())!=expected:raise ValueError('Unexpected V34 archive hash')
    if out.exists():raise ValueError('Output directory must not already exist')
    with zipfile.ZipFile(archive) as z:
        for member in z.infolist():
            if not (out/member.filename).resolve().is_relative_to(out):raise ValueError('Unsafe archive path')
        z.extractall(out)
    pkg=out/'rho5_v34_exact';manifest=pkg/'SHA256SUMS.txt'
    entries=[line.split('  ',1) for line in manifest.read_text().splitlines()]
    for h,name in entries:
        if digest((pkg/name).read_bytes())!=h:raise ValueError('Original file hash mismatch: '+name)
    p=pkg/'source/factor_graph.hpp';old=p.read_text();new=old
    for name in ('upper','reciprocal'):
        before=f'auto {name}=[&](const Big&v){{'
        if new.count(before)!=1:raise ValueError('Unexpected source')
        new=new.replace(before,f'auto {name}=[&](const Big&v) -> Rat {{')
    p.write_text(new)
    changes=[]
    for entry in entries:
        actual=digest((pkg/entry[1]).read_bytes())
        if actual!=entry[0]:
            if entry[1]!='source/factor_graph.hpp':raise ValueError('Unintended change')
            changes.append({'file':entry[1],'old_sha256':entry[0],'new_sha256':actual})
            entry[0]=actual
    manifest.write_text('\n'.join('  '.join(entry) for entry in entries)+'\n')
    receipt={'original_archive_sha256':expected,'changes':changes,'models_and_trees_unchanged':True,'independent_replay_required':True}
    (out/'FIX_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
