#!/usr/bin/env python3
"""Rebuild one frozen source/roots, then replay its tree without any LP solver."""
from pathlib import Path
import argparse,gzip,hashlib,json,shutil,subprocess,tempfile
from build_model import make_model,headers
from make_contact_case import add_case
ROOT=Path(__file__).resolve().parent

def verify_task(d,tree=None,allow_open=False):
 d=Path(d).resolve();data=json.loads((d/'model.json').read_text())
 re=make_model(data['K'],data['J'],data['type'],data['extra_anchor'],data.get('norm_coupling',False))
 if 'contact_case' in data:re=add_case(re,int(data['contact_case']['id']))
 for key in ['variables','target','K','J','type','low_r','fold_I','extra_anchor','root_denominator','root_numerators','pairs','rows']:
  if re[key]!=data[key]:raise ValueError('frozen source/root mismatch: '+key)
 if data.get('contact_case')!=re.get('contact_case'):raise ValueError('contact case mismatch')
 if 'subdomain'in data:raise ValueError('ad-hoc subroots are not a full frozen task; graft them into the certified original root first')
 expected=['k','r','w','A','B','c','d','p','e','be']+[f'{v}{i}'for v in ('u','x','v','q')for i in range(3)]+['G']
 if data['variables']!=expected:raise ValueError('rank-one oracle native dictionary mismatch')
 if tree is None:
  tree=d/'checkpoint.tree';tree=tree if tree.exists()else d/'checkpoint.tree.gz'
 tree=Path(tree).resolve()
 with tempfile.TemporaryDirectory(prefix='rho5_task_verify_')as td:
  t=Path(td);headers(re,t)
  for fn in ['mc_exact_kernel.hpp','rankone_oracle.hpp','mc_verify.cpp']:shutil.copyfile(ROOT/'source'/fn,t/fn)
  subprocess.run(['g++','-O3','-std=c++17','mc_verify.cpp','-o','verify'],cwd=t,check=True)
  tmp=t/'tree.txt'
  if tree.suffix=='.gz':
   with gzip.open(tree,'rb')as f,tmp.open('wb')as g:shutil.copyfileobj(f,g)
  else:shutil.copyfile(tree,tmp)
  args=[str(t/'verify'),str(tmp)]+(['--allow-open']if allow_open else[])
  p=subprocess.run(args,text=True,capture_output=True)
  if p.returncode:raise RuntimeError(p.stderr.strip())
  out=json.loads(p.stdout);out['model_sha256']=hashlib.sha256((d/'model.json').read_bytes()).hexdigest();out['scope']={'K':data['K'],'J':data['J'],'type':data['type'],'r_le_k':True,'F_ge':data['target'],'contact_case':data.get('contact_case')}
  return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('model_dir',type=Path);ap.add_argument('--tree',type=Path);ap.add_argument('--allow-open',action='store_true');a=ap.parse_args();print(json.dumps(verify_task(a.model_dir,a.tree,a.allow_open),indent=2))
if __name__=='__main__':main()
