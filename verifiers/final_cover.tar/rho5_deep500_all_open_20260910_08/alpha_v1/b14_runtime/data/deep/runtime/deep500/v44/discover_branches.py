"""Untrusted bounded discovery of a full post-U41 image cover.
This module may use SciPy; branch_protocol.py never imports it.
An interrupted batch leaves an explicit OPEN, never a false contradiction.
"""
from pathlib import Path
import os,time,json,copy
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
 os.environ[key]='1'
from branch_protocol import wrap,verify,prefix_image
from v44_bootstrap import db,fs,Q
from discovery import atomic_json,bound_proposals
from proposal import propose_rows

def _split_axis(rows,boxes,profile):
 import numpy as np
 from scipy.optimize import linprog
 n=len(boxes);center=np.array([float((b.lo+b.hi)/2)for b in boxes]);half=np.array([float((b.hi-b.lo)/2)for b in boxes])
 matrix=np.zeros((len(rows),n));rhs=np.zeros(len(rows))
 for i,(a,b)in enumerate(rows):
  rhs[i]=float(b)
  for j,c in a.items():matrix[i,j]=float(c)
 b=rhs-matrix@center;a=matrix*half
 scale=np.maximum(1e-9,np.maximum(abs(b),np.max(abs(a),axis=1)))
 objective=np.zeros(n);objective[23]=-half[23]
 result=linprog(objective,A_ub=a/scale[:,None],b_ub=b/scale,bounds=[(-1,1)]*n,method='highs',options={'time_limit':1.0})
 score=half[:24]*0.001
 polys=fs.BASE_POLYS+(db.WINDOW_ROWS if profile in ('PIVOT','PIVOT_CYCLE')else[])
 pairs=sorted({m for _,p in polys for m in p if len(m)==2})
 if n!=24+len(pairs):raise ValueError('Unrecognized discovery column layout')
 if result.success:
  x=center+half*result.x
  for h,(i,j)in enumerate(pairs):
   error=abs(x[24+h]-x[i]*x[j])
   if i==j:score[i]+=error
   else:
    den=half[i]+half[j]+1e-100
    score[i]+=error*half[i]/den;score[j]+=error*half[j]/den
 axis=int(np.argmax(score))
 if boxes[axis].lo>=boxes[axis].hi:raise ValueError('No nondegenerate split available')
 return axis

def _has_open(node):
 term=node['terminal']
 if term['kind']=='O':return True
 if term['kind']=='S':return _has_open(term['left'])or _has_open(term['right'])
 return False

def discover(parent,output,seconds=120,nodes=511,depth=20,profile='PIVOT_CYCLE',waves_per_node=0):
 if seconds<0 or not 1<=nodes<=1000000 or not 0<=depth<=100 or not 0<=waves_per_node<=8:raise ValueError('Invalid discovery budget')
 db.validate_profile(profile)
 output=Path(output);start=time.monotonic()
 if output.exists():
  cert=json.loads(output.read_text());prior=verify(parent,cert,True,True)
  if cert['profile']!=profile:raise ValueError('Cannot change a continued profile')
  if prior['status']!='OPEN':return prior
 else:
  cert=wrap(parent,{'waves':[],'terminal':{'kind':'O'}},profile)
  verify(parent,cert,True,True)
 out,old=prefix_image(parent,False)
 atomic_json(output,cert)
 deadline=time.monotonic()+seconds;new_nodes=0;new_splits=0;visits=0
 def save():atomic_json(output,cert)
 def visit(inbox,node,d):
  nonlocal new_nodes,new_splits,visits
  if not _has_open(node):return
  visits+=1
  o=db.common_contract(inbox,profile=profile)
  for wave in node['waves']:o=db.apply_wave(o,wave,profile=profile,cross_check=False)
  term=node['terminal']
  if term['kind']=='S':
   ax=term['axis'];b=o['aux_image'];lo,hi=map(Q,b[ax]);mid=(lo+hi)/2
   l=copy.deepcopy(b);r=copy.deepcopy(b);l[ax][1]=str(mid);r[ax][0]=str(mid)
   visit({'status':'BOUNDED','aux_image':l},term['left'],d+1)
   visit({'status':'BOUNDED','aux_image':r},term['right'],d+1)
   return
  if term['kind']!='O':return
  if time.monotonic()>=deadline or new_nodes>=nodes:return
  new_nodes+=1
  for turn in range(waves_per_node+1):
   if o['status']=='EMPTY':node['terminal']={'kind':'I'};save();return
   if fs.safe_port(o['aux_image'])is not None:node['terminal']={'kind':'A'};save();return
   if time.monotonic()>=deadline:return
   rows,boxes=db.rows_and_bounds(o['aux_image'],profile=profile)
   t=propose_rows(rows,boxes)
   if t:
    node['terminal']=t;save();return
   if turn==waves_per_node:break
   wave=bound_proposals(rows,boxes,deadline,limit=16)
   if not wave:break
   # Exact before recording. This keeps every on-disk partial tree replayable.
   o=db.apply_wave(o,wave,profile=profile,cross_check=True)
   node['waves'].append(wave);save()
  if d>=depth or new_nodes+2>nodes or time.monotonic()>=deadline:return
  ax=_split_axis(rows,boxes,profile);b=o['aux_image'];lo,hi=map(Q,b[ax]);mid=(lo+hi)/2
  if not lo<mid<hi:raise ValueError('Degenerate proposed split')
  l=copy.deepcopy(b);r=copy.deepcopy(b);l[ax][1]=str(mid);r[ax][0]=str(mid)
  node['terminal']={'kind':'S','axis':ax,'left':{'waves':[],'terminal':{'kind':'O'}},'right':{'waves':[],'terminal':{'kind':'O'}}}
  new_splits+=1;save()
  visit({'status':'BOUNDED','aux_image':l},node['terminal']['left'],d+1)
  visit({'status':'BOUNDED','aux_image':r},node['terminal']['right'],d+1)
 visit(out,cert['tree'],0)
 save();search_seconds=time.monotonic()-start
 result=verify(parent,cert,True,True)
 result.update({'new_nodes_processed':new_nodes,'new_splits_proposed':new_splits,'soft_search_seconds':seconds,'search_including_start_replay_seconds':search_seconds,'including_final_replay_seconds':time.monotonic()-start})
 atomic_json(str(output)+'.receipt.json',result)
 return result

if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('parent',type=Path);p.add_argument('--output',type=Path,required=True);p.add_argument('--seconds',type=float,default=120);p.add_argument('--nodes',type=int,default=511);p.add_argument('--depth',type=int,default=20);p.add_argument('--waves-per-node',type=int,default=0);p.add_argument('--profile',choices=db.PROFILES,default='PIVOT_CYCLE');a=p.parse_args()
 print(json.dumps(discover(json.loads(a.parent.read_text()),a.output,a.seconds,a.nodes,a.depth,a.profile,a.waves_per_node),ensure_ascii=False,indent=2))
