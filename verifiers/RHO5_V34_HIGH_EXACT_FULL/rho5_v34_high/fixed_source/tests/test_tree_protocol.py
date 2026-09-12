"""Negative controls for new P leaves, closed-root acceptance and worker ownership."""
from pathlib import Path
import sys, json, tempfile, subprocess, shutil, gzip, io
ROOT=Path(__file__).resolve().parents[1];sys.path[:0]=[str(ROOT),str(ROOT/'discovery')]
from build_models import headers,make_model
import frontier_parallel as fp
D=ROOT/'models/I200_210_high';data=json.loads((D/'model.json').read_text())
source=D/'checkpoint.tree'
if not source.exists():source=D/'checkpoint.tree.gz'
openf=gzip.open if source.suffix=='.gz' else open
# Find a genuine whole-packet exclusion and retain its exact original-root path.
chosen=None
with openf(source,'rt') as f:
 stack=[[]]
 while stack:
  path=stack.pop();row=f.readline();parts=row.split()
  if not parts:raise AssertionError('truncated actual checkpoint')
  if parts[0]=='S':
   j=int(parts[1]);stack += [path+[(j,1)],path+[(j,0)]]
  elif parts[0]=='P' and int(parts[1])<3:
   chosen=(path,row.encode());break
assert chosen is not None, 'expected a certified P graph leaf in the pilot'
steps,payload=chosen;positive=fp.envelope(steps,payload)
negative=0
with tempfile.TemporaryDirectory(prefix='v34_protocol_') as tmp:
 b=Path(tmp);headers(data,b)
 for n in ('mc_exact_kernel.hpp','rankone_oracle.hpp','factor_graph.hpp','factor_oracle.hpp','mc_verify.cpp'):
  shutil.copy2(ROOT/'source'/n,b/n)
 subprocess.run(['g++','-O2','-std=c++17','mc_verify.cpp','-o','verify'],cwd=b,check=True)
 def run(text,allow=True):
  (b/'input.tree').write_bytes(text)
  return subprocess.run([str(b/'verify'),str(b/'input.tree')]+(['--allow-open'] if allow else []),capture_output=True,text=True)
 ans=run(positive);assert ans.returncode==0,ans.stderr
 record=json.loads(ans.stdout);assert record['full_factor_leaves']==1 and record['open']==len(steps)
 for text,allow in [
  (positive,False),(b'O\n',False),(b'P 9\n',True),(b'P 0\n',True),
  (b'S 30\nO\nO\n',True),(b'S 0\nO\n',True),(b'Q\n',True),
  (b'C 1 0 -1\n',True),(b'C 1 0 0\n',True),(b'C 1 99999 1\n',True),
  (b'C 2 0 1 0 1\n',True),(positive+b'O\n',True)]:
  ans=run(text,allow);assert ans.returncode!=0,(text[:80],ans.stdout);negative+=1
 # Original-root envelopes may never consume a non-owned sibling or change ancestors.
 plan=[(0,0),(1,1)];envelope=fp.envelope(plan,b'P 1\n');env=b/'env.tree';env.write_bytes(envelope)
 out=io.BytesIO();fp.copy_focused_payload(env,plan,out);assert out.getvalue()==b'P 1\n'
 for bad in [envelope.replace(b'S 0',b'S 2',1),envelope.replace(b'O\n',b'P 1\n',1),envelope[:-2],envelope+b'O\n']:
  env.write_bytes(bad)
  try:fp.copy_focused_payload(env,plan,io.BytesIO())
  except (ValueError,IndexError):negative+=1
  else:raise AssertionError('ownership corruption was accepted')
 # The public semantic wrapper rejects any changed row before invoking its compiler.
 from verify_task import verify_task
 md=b/'bad_model';md.mkdir();changed=json.loads(json.dumps(data));changed['rows'][0]['rhs']+=1
 (md/'model.json').write_text(json.dumps(changed))
 try:verify_task(md,source,True)
 except ValueError:negative+=1
 else:raise AssertionError('mutated source model accepted')
print(json.dumps({'status':'TREE_AND_OWNERSHIP_NEGATIVE_CONTROLS_PASS','negative_controls':negative,
 'real_P_leaf_positive_envelope':True,'positive_envelope_is_not_a_complete_root':True}))
