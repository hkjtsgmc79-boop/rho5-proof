#!/usr/bin/env python3
"""Cold exact component replay. This is NOT a complete proper-B tree replay.
Uses Python 3.10+ and SymPy. SciPy is only needed with --discovery.
All mutable re-generated evidence is written in a fresh temporary copy.
"""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,tempfile,time,zipfile
ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run(cmd,cwd):
    r=subprocess.run(cmd,cwd=cwd,capture_output=True,text=True)
    print('$ '+' '.join(str(x)for x in cmd),flush=True)
    print(r.stdout,end='',flush=True)
    if r.stderr:print(r.stderr,file=sys.stderr,flush=True)
    if r.returncode:raise RuntimeError(f'Verification failed: {cmd[1]} return={r.returncode}')
    return r.stdout

def main():
    if sys.flags.optimize:raise RuntimeError('Run exact verification without Python -O/-OO')
    start=time.monotonic();manifest=json.loads((ROOT/'MANIFEST.json').read_text());count=0
    for name,h in manifest['sha256'].items():
        if sha(ROOT/name)!=h:raise ValueError(f'Hash mismatch: {name}')
        count+=1
    with tempfile.TemporaryDirectory(prefix='rho5_v37_cold_')as td:
        w=Path(td)/'rho5_v37_exact';shutil.copytree(ROOT,w,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        before={p.name:sha(p)for p in(w/'models').glob('*.json')if p.name!='example_frame.json'}
        run([sys.executable,'build_models.py'],w)
        after={p.name:sha(p)for p in(w/'models').glob('*.json')if p.name!='example_frame.json'}
        assert before==after,'semantic model regeneration mismatch'
        dep=Path(td)/'v36'
        with zipfile.ZipFile(w/'dependency/rho5_v36_exact.zip')as z:
            assert z.testzip()is None;z.extractall(dep)
        d=dep/'rho5_v36_exact'
        assert sha(d/'two_gap_certificate.json')==sha(w/'dependency/two_gap_certificate.json')
        assert sha(d/'inputs/round47/source/alpha.json')==sha(w/'dependency/alpha.json')
        bbase=json.loads((w/'models/B24_BASE.json').read_text())
        assert bbase['alpha_sha256']==sha(w/'dependency/alpha.json')
        assert bbase['two_gap_certificate_sha256']==sha(w/'dependency/two_gap_certificate.json')
        run([sys.executable,'verify_two_gap_certificate.py'],d)
        algebra=run([sys.executable,'verify_algebra.py'],w)
        run([sys.executable,'verify_capacity.py'],w)
        run([sys.executable,'verify_ports.py'],w)
        cmd=[sys.executable,'verify_protocol.py']
        if '--discovery'in sys.argv:cmd+=['--discovery']
        run(cmd,w)
        components=json.loads((w/'evidence/component_result.json').read_text())
        ports=json.loads((w/'evidence/ports_result.json').read_text())
        protocol=json.loads((w/'evidence/protocol_result.json').read_text())
        result={'status':'V37_EXACT_SIX_VARIABLE_ELIMINATION_AND_B_REPRESENTATIVES_PASS',
          'static_files_verified':count,'model_files_regenerated':len(after),
          'symbolic':json.loads(algebra.strip()),'components':components,'ports':ports,'protocol':protocol,
          'whole_B_closed':False,'macro_ledger':'14/15','unreceived_global_trees_replayed_here':False,
          'seconds':time.monotonic()-start}
    print(json.dumps(result,ensure_ascii=False),flush=True)
    return result
if __name__=='__main__':main()
