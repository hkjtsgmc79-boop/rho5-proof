#!/usr/bin/env python3
"""Fresh source rebuild and exact replay of the trees in an actual campaign state.
Default fails when any selected original root is still open.
"""
from pathlib import Path
import argparse,json,hashlib,sys
from verify_task import verify_task,ROOT

def digest(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()

def main():
 p=argparse.ArgumentParser();p.add_argument('state',type=Path,nargs='?',default=ROOT/'campaign/CURRENT_STATE.json');p.add_argument('--allow-open',action='store_true');a=p.parse_args()
 data=json.loads(a.state.read_text());out={}
 expected={'I_LOW_ALPHA','II_LOW_ALPHA'}
 if not set(data['models'])<=expected:raise ValueError('unexpected model identity')
 for n,rec in data['models'].items():
  model=ROOT/'models'/n;tree=Path(rec['tree'])
  if digest(model/'model.json')!=rec['model_sha256']or digest(tree)!=rec['tree_sha256']:raise ValueError('model/tree receipt binding failed')
  res=verify_task(model,tree,allow_open=True)
  for key in ('nodes','splits','leaves','contradiction_leaves','alpha_safe_leaves','open','max_depth','full_factor_leaves'):
   if rec[key]!=res[key]:raise ValueError('receipt differs from fresh replay '+key)
  out[n]=res
 complete=set(out)==expected and all(x['open']==0 for x in out.values())
 ans={'status':'V35_BOTH_LOW_ROOTS_ALPHA_COVERED'if complete else'V35_LOW_ALPHA_LOCALIZATION_PARTIAL','required_models':sorted(expected),'models':out,'whole_R':'OPEN','macro_ledger':'11/15'}
 (a.state.parent/'FRESH_REPLAY_RESULT.json').write_text(json.dumps(ans,indent=2)+'\n');print(json.dumps(ans,indent=2))
 if not complete and not a.allow_open:raise SystemExit(2)
if __name__=='__main__':main()
