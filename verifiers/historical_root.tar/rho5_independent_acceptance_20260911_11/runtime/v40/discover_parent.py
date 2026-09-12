#!/usr/bin/env python3
"""Optional, untrusted search. It never grafts or modifies a controller tree.
Every retained child is rechecked by the exact V40 rule before atomic save.
"""
from pathlib import Path
import argparse,json,os,time
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):os.environ[key]='1'
from protocol import *

def save(path,cert):
 path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
 tmp=path.with_name(path.name+'.tmp.'+str(os.getpid()))
 tmp.write_text(json.dumps(cert,indent=2)+'\n');os.replace(tmp,path)

def candidate(parent,label,mode):
 from proposal import propose_rows
 z=MODES[mode](parent,label)
 if z['status']=='EMPTY':return {'mode':mode,'proof':{'kind':'I'}}
 aux=z['aux_image']
 if safe_port(aux)is not None:return {'mode':mode,'proof':{'kind':'A'}}
 if mode in ('FULL','QUOTIENT'):rows,boxes=rows_for(aux,label);selections=[None]
 elif mode=='PROJECTED':rows,boxes=extended_rows(aux,label);selections=[None]
 else:
  names=[n.removeprefix('homogenized_')for n,_ in homogeneous_rows(label)]
  selections=([['S02-']]if 'S02-'in names else[])+[names]
 for sel in selections:
  if sel is not None:rows,boxes=generalized_rows(aux,label,sel)
  proof=propose_rows(rows,boxes)
  if proof:
   out={'mode':mode,'proof':proof}
   if sel is not None:out['sources']=sel
   return out
 return None

def run(item,output,seconds=120,complete_scan=False):
 start=time.monotonic();box=validate_box(item['box']);parent=parent_enclosure(box)
 path=Path(output)
 if path.exists():
  cert=json.loads(path.read_text());verify_parent(box,cert,allow_open=True)
 else:
  cert={'rule':RULE,'rule_identity':rule_identity(),'model_sha256':MODEL_SHA,
   'reported_root_sha256':REPORTED_ROOT_SHA,'box_sha256':box_hash(box),'box':box,
   'sample_ordinal':item.get('sample_ordinal'),'reported_index':item.get('index',item.get('reported_index')),
   'reported_path':item.get('path',item.get('reported_path')),'children':{g:{'mode':'OPEN','proof':{'kind':'O'}}for g in GRAPH_LABELS}}
  save(path,cert)
 for lab in GRAPH_LABELS:
  if cert['children'][lab]['mode']!='OPEN':continue
  if time.monotonic()-start>=seconds:break
  for mode in ('FULL','QUOTIENT','PROJECTED','HOMOGENEOUS'):
   if time.monotonic()-start>=seconds:break
   rec=candidate(parent,lab,mode)
   if rec is not None:
    verify_child_new(parent,lab,rec);cert['children'][lab]=rec;save(path,cert);break
  if cert['children'][lab]['mode']=='OPEN'and not complete_scan:break
 receipt=verify_parent(box,cert,allow_open=True)
 receipt.update(seconds=round(time.monotonic()-start,3),certificate=str(path),local_tree_not_modified=True)
 path.with_suffix(path.suffix+'.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 return receipt

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('box');ap.add_argument('--output',required=True)
 ap.add_argument('--seconds',type=float,default=120);ap.add_argument('--complete-scan',action='store_true')
 args=ap.parse_args();item=json.loads(Path(args.box).read_text());item=item if isinstance(item,dict)else{'box':item}
 if args.seconds<=0:raise ValueError('seconds must be positive')
 print(json.dumps(run(item,args.output,args.seconds,args.complete_scan),indent=2))
