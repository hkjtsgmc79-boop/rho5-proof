#!/usr/bin/env python3
"""Time-limited, restartable search. A checkpoint is never reported as a proof.
Usage: python run_chunks.py MODEL_DIR --seconds 600 --chunk 60 --from-tree FILE
"""
from __future__ import annotations
import argparse,hashlib,json,os,shutil,subprocess,time,gzip
from pathlib import Path

def main():
 ap=argparse.ArgumentParser();ap.add_argument('model_dir',type=Path);ap.add_argument('--seconds',type=float,default=600);ap.add_argument('--chunk',type=float,default=60);ap.add_argument('--from-tree',type=Path);ap.add_argument('--max-solves',type=int,default=1000000);a=ap.parse_args()
 d=a.model_dir.resolve();assert a.seconds>0 and a.chunk>0
 # Installed packages keep source centrally; refresh exact same frozen sources.
 source=Path(__file__).resolve().parent/'source'
 for fn in ['mc_exact_kernel.hpp','rankone_oracle.hpp','mc_verify.cpp','discover.cpp','mc_simplex_dual.hpp']:
  if not (d/fn).exists():shutil.copyfile(source/fn,d/fn)
 model_hash=hashlib.sha256((d/'model.json').read_bytes()).hexdigest()
 for exe,src in [('verify','mc_verify.cpp'),('discover','discover.cpp')]:
  if not (d/exe).exists() or (d/exe).stat().st_mtime<max(p.stat().st_mtime for p in d.glob('*.hpp')) or (d/exe).stat().st_mtime<(d/src).stat().st_mtime:
   subprocess.run(['g++','-std=c++17','-O3',src,'-o',exe],cwd=d,check=True)
 chk=d/'checkpoint.tree'
 if not chk.exists() and (d/'checkpoint.tree.gz').exists():
  with gzip.open(d/'checkpoint.tree.gz','rb') as src,chk.open('wb') as dst:shutil.copyfileobj(src,dst)
 if not chk.exists():
  if a.from_tree:shutil.copyfile(a.from_tree,chk)
  else:chk.write_text('O\n')
 # No checkpoint from a different model may be silently reused.
 identity=d/'checkpoint.model.sha256'
 if identity.exists() and identity.read_text().strip()!=model_hash:raise ValueError('Checkpoint model mismatch')
 identity.write_text(model_hash+'\n')
 start=time.monotonic();iteration=0
 logdir=d/'runs';logdir.mkdir(exist_ok=True)
 initial=subprocess.run([str(d/'verify'),str(chk),'--allow-open'],capture_output=True,text=True,check=True)
 print(initial.stdout.strip(),flush=True)
 if json.loads(initial.stdout)['open']==0:return
 while time.monotonic()-start<a.seconds:
  iteration+=1;stamp=str(time.time_ns());out=d/'checkpoint.next.tree';lg=logdir/(stamp+'.log')
  budget=min(a.chunk,max(.01,a.seconds-(time.monotonic()-start)))
  with lg.open('w') as fh:
   subprocess.run([str(d/'discover'),str(chk),str(out),str(budget),str(a.max_solves)],stdout=fh,stderr=subprocess.STDOUT,check=True)
  res=subprocess.run([str(d/'verify'),str(out),'--allow-open'],capture_output=True,text=True,check=True)
  info=json.loads(res.stdout);info.update(model_sha256=model_hash,tree_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),search_seconds=budget)
  (logdir/(stamp+'.json')).write_text(json.dumps(info,indent=2)+'\n')
  os.replace(out,chk);(d/'checkpoint.status.json').write_text(json.dumps(info,indent=2)+'\n')
  print(json.dumps(info),flush=True)
  if info['open']==0:
   # Strict acceptance, without allow-open, is mandatory on completion.
   res=subprocess.run([str(d/'verify'),str(chk)],capture_output=True,text=True,check=True)
   (d/'complete_replay.json').write_text(res.stdout)
   print('COMPLETE_FROZEN_MODEL: '+res.stdout.strip(),flush=True);return
 print('BUDGET_STOP: open leaves remain; checkpoint saved; no height claim.',flush=True)
if __name__=='__main__':main()
