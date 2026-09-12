"""Portable R53 component/selected-frontier cold replay. Not a full-root mathematical replay."""
from pathlib import Path
from collections import Counter
import argparse,gzip,hashlib,json,os,subprocess,sys,time
ROOT=Path(__file__).resolve().parent

def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def scrub(x):
 if isinstance(x,dict):return {k:scrub(v)for k,v in x.items()if k not in ('seconds','wall_seconds','source_receipt_sha256')}
 if isinstance(x,list):return [scrub(v)for v in x]
 return x
def invoke(script,args=(),json_tail=False):
 p=subprocess.run([sys.executable,str(ROOT/script),*map(str,args)],cwd=ROOT,capture_output=True,text=True)
 if p.returncode:raise RuntimeError(script+'\n'+p.stdout+'\n'+p.stderr)
 return json.loads(p.stdout.splitlines()[-1]if json_tail else p.stdout)if script.endswith(('verify_all.py','r53_port_tests.py'))else p.stdout

def main(out):
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
 start=time.monotonic();out.mkdir(parents=True)
 manifest=read(ROOT/'R53_SOURCE_MANIFEST.json')
 for n,h in manifest['files'].items():assert sha(ROOT/n)==h,n
 root_path=ROOT/'inherited/B17_ROOT.json';root_sha=sha(root_path);assert root_sha=='4b72152fec20a58eff52ab6e93a8fd082fc85a28722d762412c0c5fc17abc707'
 import r52_protocol as prior
 tree=read(root_path);stack=[(prior.structure(tree),'')];frames={r['index']:r for r in map(json.loads,gzip.open(ROOT/'inherited/OPEN_FRONTIERS.jsonl.gz','rt'))};seen=set();counts=Counter()
 for idx,node in enumerate(tree['nodes']):
  box,path=stack.pop();counts[node['kind']]+=1
  if node['kind']=='S':
   a,b=prior.tp.halve(box,node['axis']);stack.extend([(b,path+'1'),(a,path+'0')])
  elif node['kind']=='O':assert frames[idx]['path']==path and frames[idx]['box']==[v.data()for v in box];seen.add(idx)
 assert not stack and seen==set(frames)and len(seen)==754
 for s in read(ROOT/'PILOT16.json'):assert s['box']==frames[s['index']]['box']and s['path']==frames[s['index']]['path']
 print('All frozen source files and 754 actual OPEN ancestors verified.',flush=True)
 v43=invoke('v43/verify_all.py',json_tail=True);assert scrub(v43)==scrub(read(ROOT/'receipts/V43_REPLAY.json'))
 vp=out/'V43_REPLAY.json';vp.write_text(json.dumps(v43,indent=2)+'\n')
 tests=invoke('r53_port_tests.py');assert tests==read(ROOT/'receipts/PORT_TESTS.json')
 (out/'PORT_TESTS.json').write_text(json.dumps(tests,indent=2)+'\n')
 print('V43 structural proof, old/new trajectories and R/D matrix controls passed.',flush=True)
 invoke('r53_pilot.py',['--out',out/'pilot16','--receipt',vp])
 for p in (ROOT/'pilot16').glob('*.json'):
  if p.name=='HEAD_OBSTRUCTIONS.json':continue
  assert scrub(read(p))==scrub(read(out/'pilot16'/p.name)),p.name
 invoke('r53_analyze.py',['--pilot',out/'pilot16','--receipt',vp,'--out',out/'HEAD_OBSTRUCTIONS.json'])
 assert scrub(read(out/'HEAD_OBSTRUCTIONS.json'))==scrub(read(ROOT/'pilot16/HEAD_OBSTRUCTIONS.json'))
 invoke('r53_head_census.py',['--out',out/'HEAD_CENSUS754.json'])
 assert read(out/'HEAD_CENSUS754.json')==read(ROOT/'HEAD_CENSUS754.json')
 assert sha(root_path)==root_sha
 result={'status':'R53_COLD_COMPONENTS_SELECTED_PREFIXES_AND_CENSUS_PASS','frozen_source_files':len(manifest['files']),'source_manifest_sha256':sha(ROOT/'R53_SOURCE_MANIFEST.json'),'root_sha256':root_sha,'nodes':len(tree['nodes']),'kinds':dict(counts),'original_OPEN_ancestors_verified':754,'unconditional_prefixes_replayed':16,'conditional_same_source_meets_checked':4,'R_D_matrix_point_targets_checked':640,'invariant_head_census':read(ROOT/'HEAD_CENSUS754.json')['radii']['3/1000']['counts'],'full_root_mathematical_replay_performed':False,'whole_B_closed':False,'new_parent_certificates':0,'macro_ledger':'14/15','seconds':time.monotonic()-start}
 (out/'COLD_REPLAY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args();main(a.out.resolve())
