"""Versioned B42/C42 acceptance; all Round51 kinds retain their frozen meaning."""
from pathlib import Path
import hashlib,json,sys
import r51_protocol as old
ROOT=Path(__file__).resolve().parent;tp=old.tp;gp=old.gp
sys.path.insert(0,str(ROOT/'v42'))
import bound_protocol as v42
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def new_result(box,node,backend):
 result=v42.verify(gp.normalize_box(box),node,allow_open=False,cross_check=backend=='fraction')
 if result['status']not in ('EMPTY_HIGH','SAFE_ALPHA'):raise ValueError('Unpaid V42 terminal')
 return result
def verify_leaf(box,node,backend='native'):
 if not isinstance(node,dict):raise ValueError('bad terminal')
 if node.get('kind')not in ('B42','C42'):return old.verify_leaf(box,node,backend)
 return {'EMPTY_HIGH':'EMPTY','SAFE_ALPHA':'SAFE'}[new_result(box,node,backend)['status']]
def structure(data):
 if data.get('model_sha256')!=sha(tp.MODEL)or data.get('task')is not None or data.get('root_path')!='':raise ValueError('wrong original root ownership')
 nodes=data.get('nodes')
 if not isinstance(nodes,list)or not nodes:raise ValueError('empty tree')
 slots=1
 for n in nodes:
  if not isinstance(n,dict)or slots<=0:raise ValueError('bad tree envelope')
  kind=n.get('kind')
  if kind=='S':
   if set(n)!={'kind','axis'}or type(n['axis'])is not int or not 0<=n['axis']<17:raise ValueError('bad split')
   slots+=1
  elif kind=='O':
   if set(n)!={'kind'}:raise ValueError('bad O')
   slots-=1
  elif kind in ('E','C','H','V','G','U40','W40','U41','G41','B42','C42'):slots-=1
  else:raise ValueError('unknown node')
 if slots:raise ValueError('truncated tree')
 return tp.root_box()
def binding():
 rule=v42.binding(gp.normalize_box(tp.root_box()),None)['rule_identity']
 return {'schema':'ROUND52_V42_ADAPTER_V1','original_model_sha256':sha(tp.MODEL),
  'parent_tree_sha256':'dd56619d4e328241164d2aeb8ed71a5378494bef68838b01ace97120f0b7da58',
  'r51_source_manifest_sha256':sha(ROOT/'R51_SOURCE_MANIFEST.json'),
  'v41_rule_identity':old.v41.rule_identity(),'v42_rule_identity':rule,
  'v42_manifest_sha256':sha(ROOT/'v42/SHA256SUMS.json'),'adapter_sha256':sha(Path(__file__)),
  'whole_B_closed':False,'macro_ledger':'14/15'}
