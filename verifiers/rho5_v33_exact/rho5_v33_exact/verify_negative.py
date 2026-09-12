#!/usr/bin/env python3
"""Reject malformed/incomplete/noncontradictory proof inputs; never bless OPEN."""
from pathlib import Path
import subprocess,tempfile,json
from copy import deepcopy
from verify_task import verify_task
ROOT=Path(__file__).resolve().parent

def main():
 d=ROOT/'models/I214';exe=d/'verify';data=json.loads((d/'model.json').read_text());nr=len(data['rows'])+4*len(data['pairs'])
 tests={'open':'O\n','fake_safe':'Q\n','truncated':'S 4\n','bad_split':'S 99\nO\nO\n',
 'zero_support':'C 0\n','negative_weight':'C 1 0 -1\n','zero_weight':'C 1 0 0\n',
 'duplicate':'C 2 0 1 0 2\n','invalid_row':f'C 1 {nr+3} 1\n',
 'noncontradiction':'C 1 0 1\n','unknown':'PASS\n','overflow':'C 1 0 999999999999999999999999999\n',
 'bad_rank_layer':'R 8\n','false_rank_claim':'R 0\n'}
 passed=[]
 with tempfile.TemporaryDirectory() as td:
  for name,text in tests.items():
   f=Path(td)/(name+'.tree');f.write_text(text)
   p=subprocess.run([str(exe),str(f)],capture_output=True,text=True)
   assert p.returncode!=0,(name,p.stdout);passed.append(name)
  f=Path(td)/'partial.tree';f.write_text('O\n')
  r=subprocess.run([str(exe),str(f),'--allow-open'],capture_output=True,text=True,check=True)
  z=json.loads(r.stdout);assert z['open']==1 and z['status']=='R45_PARTIAL_EXACT_CHECKPOINT'
 # Frozen-source identity must reject altered model/target/G definitions too.
 with tempfile.TemporaryDirectory() as td:
  dd=Path(td)
  for kind in ['wrong_root','wrong_coefficient','wrong_target','missing_G_equality']:
   bad=deepcopy(data)
   if kind=='wrong_root':bad['root_numerators'][0][0]+=1
   elif kind=='wrong_coefficient':bad['rows'][0]['coefficients'][8]+=1
   elif kind=='wrong_target':bad['target']='1653/400'
   else:bad['rows']=[row for row in bad['rows']if row['name']!='G_def-']
   (dd/'model.json').write_text(json.dumps(bad))
   try:verify_task(dd)
   except ValueError:passed.append(kind)
   else:raise AssertionError('corrupted frozen model was not rejected: '+kind)
 out={'status':'NEGATIVE_PROOF_CONTROLS_PASS','rejected':passed,'partial_status_explicit':True}
 (ROOT/'logs/negative_controls.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
if __name__=='__main__':main()
