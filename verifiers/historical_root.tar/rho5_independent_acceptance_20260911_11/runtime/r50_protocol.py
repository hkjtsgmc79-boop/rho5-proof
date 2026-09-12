"""W40 is a complete V40 conditional cover. Frozen R49 leaf semantics stay intact."""
from pathlib import Path
import hashlib,importlib.util,json,sys
import r49_protocol as old
tp=old.tp;gp=old.gp
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'v40'))
spec=importlib.util.spec_from_file_location('_round50_v40_protocol',ROOT/'v40/protocol.py')
v40=importlib.util.module_from_spec(spec);sys.modules[spec.name]=v40;spec.loader.exec_module(v40)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def verify_leaf(box,node,backend='native'):
 if not isinstance(node,dict):raise ValueError('bad terminal record')
 if node.get('kind')=='U40':
  from r50_unconditional import verify
  return verify(box,node)
 if node.get('kind')!='W40':return old.verify_leaf(box,node,backend)
 if set(node)!={'kind','certificate'} or not isinstance(node['certificate'],dict):raise ValueError('bad W40 schema')
 b=gp.normalize_box(box);c=node['certificate']
 if v40.validate_box(c.get('box'))!=b:raise ValueError('certificate box mismatch')
 r=v40.verify_parent(b,c,allow_open=False)
 if r['children']['OPEN']:raise ValueError('unpaid W40')
 return 'SAFE' if r['children']['SAFE'] else 'EMPTY'
def structure(data):
 if data.get('model_sha256')!=sha(tp.MODEL) or data.get('task')is not None or data.get('root_path')!='':raise ValueError('wrong original root ownership')
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
  elif kind in ('E','C','H','V','G','W40','U40'):slots-=1
  else:raise ValueError('unknown node')
 if slots:raise ValueError('truncated tree')
 return tp.root_box()
def binding():
 return {'schema':'ROUND50_V40_ADAPTER_V1','model_sha256':sha(tp.MODEL),
  'parent_tree_sha256':v40.REPORTED_ROOT_SHA,'r49_source_manifest_sha256':sha(ROOT/'R49_SOURCE_MANIFEST.json'),
  'v40_rule_identity':v40.rule_identity(),'v40_manifest_sha256':sha(ROOT/'v40/MANIFEST.json'),
  'v40_dependency_zip_sha256':v40.bootstrap.ARCHIVE_SHA,'adapter_sha256':sha(Path(__file__)),'unconditional_rule_identity':__import__('r50_unconditional').identity(),
  'whole_B_closed':False,'macro_ledger':'14/15'}
