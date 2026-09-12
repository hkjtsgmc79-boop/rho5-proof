"""Explicit new B44 wrapper; every older terminal retains its original implementation."""
from pathlib import Path
import hashlib,json,subprocess,sys
import r52_protocol as old
ROOT=Path(__file__).resolve().parent;tp=old.tp;gp=old.gp
PARENT_ROOT='4b72152fec20a58eff52ab6e93a8fd082fc85a28722d762412c0c5fc17abc707'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def json_hash(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
def b44_rule_identity():
 return json_hash({'rule':'V44_POST_U41_FULL_IMAGE_BISECTION_V1','files':{n:sha(ROOT/'v44'/n)for n in ('v44_bootstrap.py','branch_protocol.py')},'U41':old.old.v41.rule_identity()})
def binding():
 return {'schema':'R54_V44_ACTUAL_ROOT_WRAPPER_V1','parent_tree_sha256':PARENT_ROOT,'model_sha256':sha(tp.MODEL),'r53_source_manifest_sha256':sha(ROOT/'R53_SOURCE_MANIFEST.json'),'r54_source_manifest_sha256':sha(ROOT/'R54_SOURCE_MANIFEST.json'),'v44_rule_identity':b44_rule_identity(),'v44_manifest_sha256':sha(ROOT/'v44/MANIFEST_SHA256.json'),'adapter_sha256':sha(Path(__file__)),'worker_sha256':sha(ROOT/'r54_b44_worker.py'),'macro_ledger':'14/15','whole_B_closed':False}
def verify_b44(box,index,path,node):
 req={'box':gp.normalize_box(box),'index':index,'path':path,'node':node}
 # V44 explicitly requires its own byte-frozen module directory. Use a fresh
 # interpreter instead of mixing its module names with old root interpreters.
 p=subprocess.run([sys.executable,'-S',str(ROOT/'r54_b44_worker.py')],input=json.dumps(req),text=True,capture_output=True)
 if p.returncode:raise ValueError('B44 strict worker rejected: '+p.stderr[-4000:])
 result=json.loads(p.stdout)
 if result['status']not in ('EMPTY','SAFE'):raise ValueError('Unpaid B44 parent')
 return result
def structure(data,require_binding=False):
 if data.get('model_sha256')!=sha(tp.MODEL)or data.get('task')is not None or data.get('root_path')!='':raise ValueError('Wrong original B17 root')
 if require_binding and data.get('r54_binding')!=binding():raise ValueError('Wrong R54 binding')
 nodes=data.get('nodes');slots=1
 if not isinstance(nodes,list)or not nodes:raise ValueError('Empty root')
 for n in nodes:
  if not isinstance(n,dict)or slots<=0:raise ValueError('Tree envelope')
  kind=n.get('kind')
  if kind=='S':
   if set(n)!={'kind','axis'}or type(n['axis'])is not int or not 0<=n['axis']<17:raise ValueError('Original split axis')
   slots+=1
  elif kind=='O':
   if n!={'kind':'O'}:raise ValueError('Bad OPEN')
   slots-=1
  elif kind in ('E','C','H','V','G','U40','W40','U41','G41','B42','C42','B44'):slots-=1
  else:raise ValueError('Unknown root terminal')
 if slots:raise ValueError('Truncated root')
 return tp.root_box()
