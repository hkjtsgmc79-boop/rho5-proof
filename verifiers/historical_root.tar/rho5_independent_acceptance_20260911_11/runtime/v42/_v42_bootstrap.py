"""Read-only extraction of received dependencies; no access to user local paths."""
from pathlib import Path
from functools import lru_cache
import atexit,hashlib,json,shutil,sys,tempfile,zipfile
ROOT=Path(__file__).resolve().parent
EXPECTED={'handoff.zip':'32884be8575bf20e747ed40e7dc18169a50af9bddf4586763c609d37c83223cc','round50.zip':'65e5bd5e7586fb9d1cd47324447ef06ac35f55e74ad76a1d1fa09e2aa8ebfa7d'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def extract(z,d):
    with zipfile.ZipFile(z)as f:
        for n in f.namelist():
            dest=(d/n).resolve()
            if not dest.is_relative_to(d.resolve()):raise ValueError('Unsafe archive member')
        f.extractall(d)
@lru_cache(None)
def prepare():
    identity=json.loads((ROOT/'accepted/IDENTITY.json').read_text())
    if identity!=EXPECTED:raise ValueError('Changed dependency identity')
    for n,h in EXPECTED.items():
        if sha(ROOT/'accepted'/n)!=h:raise ValueError('Wrong dependency '+n)
    td=Path(tempfile.mkdtemp(prefix='rho5_v42_'));atexit.register(shutil.rmtree,td,ignore_errors=True)
    extract(ROOT/'accepted/handoff.zip',td)
    h=td/'RHO5_POST_V41_R51_B01_B02'
    manifest=json.loads((h/'HANDOFF_SHA256.json').read_text())
    for n,digest in manifest.items():
        if sha(h/n)!=digest:raise ValueError('Handoff identity '+n)
    v=h/'round51/v41';shutil.copyfile(ROOT/'accepted/round50.zip',v/'dependency/RHO5_ROUND50_V40_LIGHT.zip')
    bdir=td/'b02';bdir.mkdir();extract(h/'structures/B_STRUCTURE_02_Exact_Package_2026-09-09.zip',bdir)
    return {'root':td,'handoff':h,'v41':v,'b02':bdir/'B_STRUCTURE_02','manifest_count':len(manifest)}
@lru_cache(None)
def v41_api():
    p=prepare();sys.path.insert(0,str(p['v41']))
    import v41_protocol,dual_box,source_access
    return v41_protocol,dual_box,source_access
@lru_cache(None)
def b02_api():
    p=prepare();sys.path.insert(0,str(p['b02']))
    import b_structure_02
    return b_structure_02

def centers():
    return [c['center']for c in json.loads((prepare()['b02']/'accepted_inputs/local_wall_certificate.json').read_text())['cases']]

def canonical_hash(obj):
    return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
