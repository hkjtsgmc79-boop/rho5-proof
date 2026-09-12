#!/usr/bin/env python3
"""Optional numerical proposals; returned C/H certificates are exact-checked.
The SciPy/HiGHS status never constitutes an accepted result.
"""
from __future__ import annotations
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
from pathlib import Path
import json,time
import numpy as np
from scipy.optimize import linprog
from graph_protocol import *

def lp_propose(aux,label):
 rows,boxes=rows_for(aux,label)
 center=np.array([float((b.lo+b.hi)/2)for b in boxes]);half=np.array([float((b.hi-b.lo)/2)for b in boxes])
 mat=np.zeros((len(rows),N));rhs=np.zeros(len(rows))
 for i,(a,b)in enumerate(rows):
  rhs[i]=float(b)
  for j,c in a.items():mat[i,j]=float(c)
 bb=rhs-mat@center;aa=mat*half
 norm=np.maximum(1e-9,np.maximum(np.abs(bb),np.max(np.abs(aa),axis=1)))
 aa/=norm[:,None];bb/=norm
 def rationalize(lambdas,kind):
  if not np.all(np.isfinite(lambdas)):return None
  for scale in (10**7,10**10,10**13):
   ww=[max(0,int(round(float(v)*scale)))for v in lambdas]
   rec={'kind':kind,'weights':[[i,w]for i,w in enumerate(ww)if w]}
   if kind=='H':rec['objective_weight']=scale
   if not rec['weights']:continue
   try:
    m=exact_margin(aux,label,rec)
    if (kind=='C'and m<0)or(kind=='H'and m<=0):return rec
   except(ValueError,ZeroDivisionError):pass
  return None
 phase=np.column_stack([aa,-np.ones(len(rows))]);obj=np.zeros(N+1);obj[-1]=1
 res=linprog(obj,A_ub=phase,b_ub=bb,bounds=[(-1,1)]*N+[(0,None)],method='highs',options={'time_limit':2})
 if res.success and res.fun>1e-10:
  rec=rationalize(-res.ineqlin.marginals/norm,'C')
  if rec:return rec
 obj=np.zeros(N);obj[FI]=-half[FI]
 res=linprog(obj,A_ub=aa,b_ub=bb,bounds=[(-1,1)]*N,method='highs',options={'time_limit':2})
 if res.success:
  rec=rationalize(-res.ineqlin.marginals/norm,'H')
  if rec:return rec
 return None

def discover_cover(box):
 started=time.monotonic();parent=parent_enclosure(box);children={};counts={};kept=[]
 for label in GRAPH_LABELS:
  out=contract_chart(parent,label)
  if out['status']=='EMPTY':rec={'kind':'I'}
  elif safe_port(out['aux_image'])is not None:rec={'kind':'A'}
  else:
   kept.append({'label':label,'prefix':{NAMES[i]:out['aux_image'][i]for i in(8,9,10)}})
   rec=lp_propose(out['aux_image'],label)or{'kind':'O'}
  children[label]=rec;counts[rec['kind']]=counts.get(rec['kind'],0)+1
 cert={'rule':RULE,'rule_identity':rule_identity(),'model_sha256':sha(paths.FROZEN/'models/B17_FULL.json'),'box_sha256':box_hash(box),'children':children}
 return cert,{'counts':counts,'seconds':time.monotonic()-started,'surviving_after_interval':kept}

if __name__=='__main__':
 import argparse
 a=argparse.ArgumentParser();a.add_argument('box');a.add_argument('--output',required=True);s=a.parse_args()
 b=json.loads(Path(s.box).read_text());b=b.get('box',b)if isinstance(b,dict)else b
 cert,stats=discover_cover(b);Path(s.output).write_text(json.dumps(cert,indent=2)+'\n')
 print(json.dumps(stats,indent=2))
