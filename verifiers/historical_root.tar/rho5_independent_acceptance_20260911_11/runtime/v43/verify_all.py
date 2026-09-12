"""Portable cold replay: new local certificates and selected R52 diagnostic only."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parent

def require(test,msg):
    if not test:raise ValueError(msg)
def check_files():
    manifest=json.loads((ROOT/'MANIFEST_SHA256.json').read_text())
    for name,digest in manifest.items():
        p=ROOT/name;require(p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==digest,'Manifest mismatch '+name)
    return len(manifest)
def invoke(name):
    p=subprocess.run([sys.executable,str(ROOT/name)],cwd=ROOT,capture_output=True,text=True)
    if p.returncode:
        print(p.stdout);print(p.stderr,file=sys.stderr);raise ValueError('Component failed '+name)
    try:res=json.loads(p.stdout)
    except json.JSONDecodeError:res=json.loads(p.stdout.strip().splitlines()[-1])
    return res

def scrub_times(obj):
    if isinstance(obj,dict):return {k:scrub_times(v)for k,v in obj.items()if k!='seconds'}
    if isinstance(obj,list):return [scrub_times(v)for v in obj]
    return obj

def main(local_only=False):
    t=time.monotonic();count=check_files();print('Static file hashes:',count,flush=True)
    local=invoke('local_guard.py');require(local['status']=='V43_SIX_CHARTS_EIGHT_INWARD_DIRECTIONS_PASS','local status')
    controls=invoke('verify_controls.py');require(controls['status']=='V43_EXACT_P0_BOUNDARY_CONTROLS_PASS','control status')
    neg=invoke('verify_negative.py');require(neg['rejected']==17,'negative test count')
    for record,fn in [(local,'local_certificate_replay.json'),(controls,'control_replay.json'),(neg,'negative_replay.json')]:
        expected=json.loads((ROOT/'evidence'/fn).read_text());require(record==expected,'Recalculated evidence mismatch '+fn)
    print('Six charts, eight directions, physical controls and 17 negative tests passed.',flush=True)
    diagnostic=None
    if not local_only:
        diagnostic=invoke('replay_frontier_diagnostic.py')
        expected=json.loads((ROOT/'evidence/r52_rebase.json').read_text())
        require(scrub_times(diagnostic)==scrub_times(expected),'Fresh old/new conditional replay differs')
        require(len(diagnostic['records'])==2,'two original box controls')
        require(all(c['meet_status']=='BOUNDED' and c['meet_equals_old'] and c['old_conditional_inside_current_unconditional']
            for r in diagnostic['records']for c in r['children']),'four persistent graphs remain explicitly unpaid')
        print('Two received old/current U41 prefixes and four conditioned trajectories replayed; all four remain unpaid.',flush=True)
    result=dict(status='V43_LOCAL_ONLY_COMPONENTS_PASS'if local_only else'V43_P0_BOUNDARY_AND_R52_DIAGNOSTICS_PASS_NOT_GLOBAL_CLOSURE',
      static_files_checked=count,radius=local['radius'],charts=6,certified_ascent_directions=8,
      original_inward_directions=6,switched_tangent_directions=2,B_single_slack=local['single_slack'],
      X_boundary_controls=2,canonical_proper_B_boundary_control=1,negative_tests=17,
      R52_full_189_parent_coverage_replayed=False,unreceived_Round52_full_tree_replayed_here=False,
      new_complete_parent_certificates=0,new_alpha_safe_parent_certificates=0,
      round52_baseline_open=754,original_tree_modified=False,macro_ledger='14/15',whole_B_closed=False,
      R52_diagnostic=diagnostic,seconds=time.monotonic()-t)
    print(json.dumps(result,ensure_ascii=False));return result
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--local-only',action='store_true');a=ap.parse_args();main(a.local_only)
