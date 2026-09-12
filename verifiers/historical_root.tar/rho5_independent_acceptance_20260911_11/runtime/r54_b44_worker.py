"""Fresh-process V44 worker: enforces its frozen dependency namespace and actual ownership."""
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'v44'))
from controller_adapter import verify_at_actual_leaf

def run(req):
 if not isinstance(req,dict)or set(req)!={'box','index','path','node'}:raise ValueError('actual context schema')
 node=req['node']
 if not isinstance(node,dict)or set(node)!={'kind','parent','certificate'}or node['kind']!='B44':raise ValueError('B44 root wrapper schema')
 p=node['parent']
 if not isinstance(p,dict)or set(p)!={'index','path','box','box_sha256','partial_certificate','sample'}:raise ValueError('B44 parent schema')
 if p['sample']is not None and(type(p['sample'])is not int or p['sample']<0):raise ValueError('sample label')
 return verify_at_actual_leaf(req['box'],req['index'],req['path'],p,node['certificate'])
if __name__=='__main__':print(json.dumps(run(json.load(sys.stdin)),separators=(',',':')))
