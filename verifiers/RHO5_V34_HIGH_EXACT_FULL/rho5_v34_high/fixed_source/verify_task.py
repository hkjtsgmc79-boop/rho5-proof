#!/usr/bin/env python3
from pathlib import Path
import argparse,json,hashlib,tempfile,subprocess,shutil,gzip
from build_models import make_model,headers
ROOT=Path(__file__).resolve().parent
SOURCE_NAMES=('mc_exact_kernel.hpp','rankone_oracle.hpp','factor_graph.hpp','factor_oracle.hpp','mc_verify.cpp')
def verify_task(path,tree=None,allow_open=False):
 d=Path(path).resolve();data=json.loads((d/'model.json').read_text())
 regen=make_model(data['K'],data['J'],data['type'],data['branch'])
 if data!=regen:raise ValueError('frozen mathematical model mismatch')
 if 'subdomain'in data:raise ValueError('subroot alone has no original-root coverage credit')
 if tree is None:
  tree=d/'checkpoint.tree'
  if not tree.exists():tree=d/'checkpoint.tree.gz'
 tree=Path(tree).resolve()
 with tempfile.TemporaryDirectory(prefix='rho5_v34_verify_') as tmp:
  b=Path(tmp);headers(regen,b)
  for n in SOURCE_NAMES:shutil.copy2(ROOT/'source'/n,b/n)
  compile=subprocess.run(['g++','-O3','-std=c++17','mc_verify.cpp','-o','verify'],cwd=b,text=True,capture_output=True)
  if compile.returncode:raise RuntimeError(compile.stderr)
  if tree.suffix=='.gz':
   with gzip.open(tree,'rb')as f,(b/'tree').open('wb')as g:shutil.copyfileobj(f,g)
   tree=b/'tree'
  r=subprocess.run([str(b/'verify'),str(tree)]+(['--allow-open']if allow_open else[]),text=True,capture_output=True)
  if r.returncode:raise RuntimeError(r.stderr)
  ans=json.loads(r.stdout)
 ans['model_sha256']=hashlib.sha256((d/'model.json').read_bytes()).hexdigest()
 ans['scope']={k:data[k]for k in ('K','J','type','branch','target','actual_r_relation')}
 return ans
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('model',type=Path);p.add_argument('--tree',type=Path);p.add_argument('--allow-open',action='store_true');a=p.parse_args()
 print(json.dumps(verify_task(a.model,a.tree,a.allow_open),indent=2))
