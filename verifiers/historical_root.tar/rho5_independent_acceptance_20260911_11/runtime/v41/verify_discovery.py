"""Optional SciPy smoke test. Not part of the optimizer-free exact replay."""
from pathlib import Path
import json,tempfile,subprocess,sys,time
from source_access import ROOT,SOURCE
from discovery import discover_parent
from v41_protocol import verify

def run():
    samples=json.loads((SOURCE/'REMAINING_SAMPLES64.json').read_text());start=time.time()
    with tempfile.TemporaryDirectory(prefix='v41_smoke_')as td:
        td=Path(td)
        z=discover_parent(samples[49]['box'],td/'zero.json',seconds=0,max_waves=0)
        assert z['status']=='OPEN';assert verify(samples[49]['box'],json.loads((td/'zero.json').read_text()),allow_open=True)['status']=='OPEN'
        a=discover_parent(samples[0]['box'],td/'single.json',seconds=30,max_waves=3)
        assert a['status']=='EMPTY'
        before=(td/'single.json').read_bytes()
        b=discover_parent(samples[0]['box'],td/'single.json',seconds=0,max_waves=3)
        assert b['status']=='EMPTY'and (td/'single.json').read_bytes()==before
        try:discover_parent(samples[1]['box'],td/'single.json',seconds=0,max_waves=3)
        except ValueError:pass
        else:raise AssertionError('Wrong box resume accepted')
        try:discover_parent(samples[0]['box'],td/'single.json',profile='CYCLE',seconds=0,max_waves=3)
        except ValueError:pass
        else:raise AssertionError('Wrong profile resume accepted')
        (td/'two.json').write_text(json.dumps([samples[0],samples[5]]))
        run=subprocess.run([sys.executable,str(ROOT/'scan_frontiers.py'),str(td/'two.json'),'--output',str(td/'scan'),'--workers','2','--limit','2','--max-waves','3','--seconds-per-parent','30'],cwd=ROOT,text=True,capture_output=True,timeout=90)
        if run.returncode:raise RuntimeError(run.stdout+run.stderr)
        report=json.loads((td/'scan/SCAN_RESULTS.json').read_text())
        assert len(report['results'])==2
        for r in report['results']:
            assert r['result']['status']=='EMPTY'
            node=json.loads(Path(r['certificate']).read_text());item=[samples[0],samples[5]][r['ordinal']]
            assert verify(item['box'],node,cross_check=True)['status']=='EMPTY'
    return dict(status='V41_OPTIONAL_DISCOVERY_SMOKE_PASS',zero_budget_preserves_OPEN=True,
       successful_single_parent=True,unchanged_closed_resume=True,wrong_box_and_profile_rejected=True,
       two_workers_two_independent_parents=True,tested_40_workers_here=False,seconds=time.time()-start)
if __name__=='__main__':print(json.dumps(run(),indent=2))
