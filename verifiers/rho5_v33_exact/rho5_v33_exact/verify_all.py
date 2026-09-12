#!/usr/bin/env python3
"""V33 complete low-r band verification. No discovery or optimizer is called."""
from pathlib import Path
import gzip,hashlib,json,shutil,subprocess,sys,tempfile,time
from verify_task import verify_task
from verify_fraction import run as fraction_replay
ROOT=Path(__file__).resolve().parent

def main():
 start=time.monotonic()
 if (ROOT/'SHA256SUMS.txt').exists():
  for line in (ROOT/'SHA256SUMS.txt').read_text().splitlines():
   digest,name=line.split('  ',1)
   if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:raise ValueError('SHA256 mismatch: '+name)
 (ROOT/'logs').mkdir(exist_ok=True)
 for script in ['check_handoff.py','verify_semantics.py','verify_transport.py','verify_model.py']:
  args=[sys.executable,str(ROOT/script)]
  if script=='check_handoff.py':args+=[str(ROOT/'sources/handoff.md')]
  subprocess.run(args,check=True)
 results=[];cross=[]
 for name in ['I214','II214']:
  d=ROOT/'models'/name
  ans=verify_task(d);assert ans['open']==0
  assert ans['scope']['K']=='107/50'and ans['scope']['J']=='43/20'and ans['scope']['contact_case']is None
  print(name,json.dumps(ans),flush=True);results.append(ans)
  with tempfile.TemporaryDirectory(prefix='fraction_partition_')as td:
   tmp=Path(td)/'tree.txt'
   tree=d/'checkpoint.tree.gz'
   if tree.exists():
    with gzip.open(tree,'rb')as f,tmp.open('wb')as g:shutil.copyfileobj(f,g)
   else:shutil.copyfile(d/'checkpoint.tree',tmp)
   z=fraction_replay(d/'model.json',tmp);assert z['open']==0;assert z['nodes']==ans['nodes']
   cross.append(z);print(name,'independent partition/fraction sample',json.dumps({k:v for k,v in z.items()if k!='samples'}),flush=True)
 # Compile local test-only copy for negative and cross-arithmetic control scripts.
 d=ROOT/'models/I214'
 for fn in ['mc_exact_kernel.hpp','rankone_oracle.hpp','mc_verify.cpp']:shutil.copyfile(ROOT/'source'/fn,d/fn)
 subprocess.run(['g++','-O3','-std=c++17','mc_verify.cpp','-o','verify'],cwd=d,check=True)
 for script in ['verify_rankone.py','verify_negative.py']:subprocess.run([sys.executable,str(ROOT/script)],check=True)
 # Offline checkpoints remain explicitly partial, not part of this height credit.
 partial=[]
 for name in ['I210','II210','I210_214','II210_214']:
  if (ROOT/'models'/name/'model.json').exists():
   z=verify_task(ROOT/'models'/name,allow_open=True);partial.append(z);print('OFFLINE CHECKPOINT',name,json.dumps(z),flush=True)
 out={'status':'V33_COMPLETE_LOW_R_214_215_PASS','new_theorem':'Full real X, 107/50<=k<=43/20 and r<=k => F<4132517/1000000','inherited_extension':'With frozen Round44 high-r and K19/K24: all k>=107/50 are safe','complete_models':results,'nodes':sum(t['nodes']for t in results),'leaves':sum(t['leaves']for t in results),'open':0,'fraction_cross_checks':[{k:v for k,v in z.items()if k!='samples'}for z in cross],'offline_checkpoints':partial,'whole_R':'OPEN','macro_B22':'OPEN','ledger':'11/15','seconds':time.monotonic()-start}
 (ROOT/'logs/v33_final_verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
