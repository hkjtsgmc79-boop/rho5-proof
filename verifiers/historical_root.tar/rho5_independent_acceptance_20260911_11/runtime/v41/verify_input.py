from pathlib import Path
import hashlib,json
from source_access import ROOT,SOURCE,IDENTITY,ARCHIVE,fs

def run():
    manifest=json.loads((SOURCE/'R50_SOURCE_MANIFEST.json').read_text())
    bad=[]
    for name,digest in manifest['files'].items():
        path=SOURCE/name
        if not path.is_file()or hashlib.sha256(path.read_bytes()).hexdigest()!=digest:bad.append(name)
    if bad:raise ValueError('Frozen Round50 source mismatch: '+str(bad))
    a=json.loads((SOURCE/'receipts/FROZEN_ROOT_REPLAY.json').read_text())
    b=json.loads((SOURCE/'receipts/COLD_REPLAY.json').read_text())
    fields=('nodes','splits','contradictions','alpha_safe','open','max_depth','tree_sha256','model_sha256','source_manifest_sha256')
    for k in fields:
        if a[k]!=b[k]:raise ValueError('Receipt mismatch '+k)
    if a['tree_sha256']!=IDENTITY['reported_root_sha256']or a['open']!=8553:raise ValueError('Wrong reported root')
    if a['source_manifest_sha256']!=hashlib.sha256((SOURCE/'R50_SOURCE_MANIFEST.json').read_bytes()).hexdigest():raise ValueError('Receipt/source binding')
    samples=json.loads((SOURCE/'REMAINING_SAMPLES64.json').read_text())
    if len(samples)!=64 or len({s['index']for s in samples})!=64:raise ValueError('Bad sample list')
    for s in samples:
        if fs.box_hash(s['box'])!=s['box_sha256']:raise ValueError('Sample bounds/hash mismatch')
    return dict(frozen_round50_file_hashes_checked=len(manifest['files']),sample_boxes=64,
                local_receipts_matching_fields=list(fields),reported_open=8553,
                unreceived_round50_tree_replayed_here=False,full_ancestry_verified_here=False)
if __name__=='__main__':print(json.dumps(run(),indent=2))
