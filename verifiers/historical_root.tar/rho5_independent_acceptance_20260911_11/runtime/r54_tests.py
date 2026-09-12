"""Concrete B44 actual-owner integration checks; V44's own29 controls are separate."""
from pathlib import Path
from copy import deepcopy
import json,time
import r54_protocol as p
W=Path(__file__).resolve().parent
def read(f):return json.loads(f.read_text())
def size(n):
 t=n['terminal'];return 1 if t['kind']!='S'else 1+size(t['left'])+size(t['right'])
def main():
 start=time.monotonic();records=[read(f)for f in (W/'import21').glob('result_*.json')];r=min(records,key=lambda r:size(r['node']['certificate']['tree']))
 assert p.b44_rule_identity()==r['node']['certificate']['rule_identity']
 positive=p.verify_b44(r['box'],r['index'],r['path'],r['node']);assert positive['status']=='EMPTY'
 controls=[]
 def reject(name,box,idx,path,node):
  try:p.verify_b44(box,idx,path,node)
  except ValueError as e:controls.append({'name':name,'rejected':True,'reason':str(e).splitlines()[-1]});return
  raise AssertionError('Accepted '+name)
 reject('wrong_actual_index',r['box'],r['index']+1,r['path'],r['node'])
 reject('wrong_actual_path',r['box'],r['index'],r['path']+'0',r['node'])
 b=deepcopy(r['box']);b[0]=['0','0'];reject('wrong_actual_box',b,r['index'],r['path'],r['node'])
 n=deepcopy(r['node']);n['cached_image']=[];reject('cached_outer_image',r['box'],r['index'],r['path'],n)
 n=deepcopy(r['node']);n['parent']['sample']=True;reject('boolean_sample',r['box'],r['index'],r['path'],n)
 n=deepcopy(r['node']);n['certificate']['rule_identity']='0'*64;reject('wrong_rule_identity',r['box'],r['index'],r['path'],n)
 n=deepcopy(r['node']);n['certificate']['tree']={'waves':[],'terminal':{'kind':'O'}};reject('unpaid_local_root',r['box'],r['index'],r['path'],n)
 # Dispatch a real old simple terminal through the new replay route and compare
 # its result with the frozen route on exactly the same ancestor interval.
 import r54_replay as replay
 root=read(W/'inherited/B17_ROOT.json');stack=[(p.structure(root),'')]
 for idx,node in enumerate(root['nodes']):
  b,path=stack.pop()
  if node['kind']=='S':
   l,u=p.tp.halve(b,node['axis']);stack.extend([(u,path+'1'),(l,path+'0')])
  elif node['kind']in ('C','E'):
   old=replay.prior.check_chunk(('native',[(b,node)]));new=replay.check_chunk(('native',[(b,node,idx,path)]));assert old==new;break
 else:raise AssertionError('No inherited simple terminal')
 result={'status':'R54_B44_ACTUAL_OWNER_INTEGRATION_PASS','positive_parent':r['index'],'positive':positive,'rule_identity_matches_frozen_V44':True,'negative_controls':controls,'old_terminal_dispatch_identical':{'index':idx,'kind':node['kind'],'receipt':old},'no_positive_H_or_A_claim':True,'seconds':time.monotonic()-start}
 (W.parent/'INTEGRATION_TESTS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
