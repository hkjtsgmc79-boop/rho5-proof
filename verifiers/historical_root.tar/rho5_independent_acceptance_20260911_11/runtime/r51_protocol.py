"""Versioned U41/G41 exact trace acceptance; frozen Round50 terminal semantics retained."""
from pathlib import Path
import hashlib,json,sys
import r50_protocol as old
ROOT=Path(__file__).resolve().parent;tp=old.tp;gp=old.gp
sys.path.insert(0,str(ROOT/'v41'))
import v41_protocol as v41
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def verify_leaf(box,node,backend='native'):
 if not isinstance(node,dict):raise ValueError('bad terminal')
 if node.get('kind')not in ('U41','G41'):return old.verify_leaf(box,node,backend)
 result=v41.verify(gp.normalize_box(box),node,allow_open=False,cross_check=backend=='fraction')
 if result['status']not in ('EMPTY','SAFE'):raise ValueError('unpaid V41 terminal')
 return result['status']
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
  elif kind in ('E','C','H','V','G','U40','W40','U41','G41'):slots-=1
  else:raise ValueError('unknown node')
 if slots:raise ValueError('truncated tree')
 return tp.root_box()
def binding():
 return {'schema':'ROUND51_V41_ADAPTER_V1','original_model_sha256':sha(tp.MODEL),
  'parent_tree_sha256':v41.IDENTITY['reported_root_sha256'],'r50_source_manifest_sha256':sha(ROOT/'R50_SOURCE_MANIFEST.json'),
  'v41_rule_identity':v41.rule_identity(),'v41_manifest_sha256':sha(ROOT/'v41/MANIFEST.json'),
  'v41_dependency_zip_sha256':v41.IDENTITY['received_zip_sha256'],'adapter_sha256':sha(Path(__file__)),
  'whole_B_closed':False,'macro_ledger':'14/15'}
