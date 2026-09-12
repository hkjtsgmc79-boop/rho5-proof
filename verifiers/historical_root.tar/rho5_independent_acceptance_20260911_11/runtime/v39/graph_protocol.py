#!/usr/bin/env python3
"""Independent rational verifier for a complete finite prefix-chart cover.
C/H always use the actual F auxiliary coordinate. All 189 children must be
checked. OPEN is permitted only in explicitly partial review, never completion.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import json,hashlib
import paths
from graph_contract import *
from relaxation import rows_and_bounds,FI
from interval_capacity import CENTERS

RULE='V39_PREFIX_GRAPH_V1'
RULE_FILES=('prefix_graph.py','graph_contract.py','graph_protocol.py')

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rule_identity():
 files={n:sha(paths.ROOT/n)for n in RULE_FILES}
 for n in ('capacity.py','interval_capacity.py','high_value_contraction.py','relaxation.py','models/B24_BASE.json','models/B17_FULL.json','dependency/alpha.json','dependency/two_gap_certificate.json'):
  files['round48/'+n]=sha(paths.FROZEN/n)
 return hashlib.sha256(json.dumps(files,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def normalize_box(box):
 if not isinstance(box,(tuple,list))or len(box)!=17:raise ValueError('Expected original 17-coordinate box')
 return [(v if isinstance(v,I)else I(*v)).data()for v in box]
def box_hash(box):return hashlib.sha256(json.dumps(normalize_box(box),separators=(',',':')).encode()).hexdigest()

def safe_port(aux):
 b=[I(*v)for v in aux]
 if b[23].hi<=ALPHA:return {'port':'height'}
 sig=(b[1]-b[2]).intersection(I(0,b[1].hi));tau=(b[1]-b[3]).intersection(I(0,b[1].hi))
 if sig is None or tau is None:return None
 gap=[b[0],b[1],-b[1],*b[4:23],sig,tau]
 assert len(gap)==24
 for j,c in enumerate(CENTERS):
  budget=max(max(abs(v.lo-a),abs(v.hi-a))for v,a in zip(gap,c))+3*(sig.hi+tau.hi)
  if budget<Q(1,1250):return {'port':f'V36_two_gap_{j}','budget':str(budget)}
 return None

def rows_for(aux,label):
 rows,boxes=rows_and_bounds(aux)
 return rows+closed_rows(CHARTS[label][0]),boxes

def exact_margin(aux,label,record):
 if record.get('kind')not in('C','H'):raise ValueError('Not C/H')
 expected={'kind','weights'} if record['kind']=='C'else {'kind','weights','objective_weight'}
 if set(record)!=expected:raise ValueError('C/H schema mismatch')
 rows,boxes=rows_for(aux,label);co=[Q(0)]*N;rhs=Q(0);seen=set()
 w=record.get('weights')
 if not isinstance(w,list)or not w:raise ValueError('Empty dual support')
 for pair in w:
  if not isinstance(pair,list)or len(pair)!=2:raise ValueError('Bad dual pair')
  idx,weight=pair
  if type(idx)is not int or type(weight)is not int or not 0<=idx<len(rows)or weight<=0 or idx in seen:raise ValueError('Invalid or repeated row/weight')
  seen.add(idx);a,bb=rows[idx];rhs+=weight*bb
  for i,c in a.items():co[i]+=weight*c
 if record['kind']=='H':
  t=record['objective_weight']
  if type(t)is not int or t<=0:raise ValueError('Positive integer objective weight required')
  co[FI]-=t
 v=rhs-sum(min(c*b.lo,c*b.hi)for c,b in zip(co,boxes))
 if record['kind']=='H':v-=t*ALPHA
 return v

def verify_child(parent,label,record, *, allow_open=False):
 if label not in GRAPH_LABELS:raise ValueError('Unknown graph')
 if not isinstance(record,dict):raise ValueError('Invalid child record')
 out=contract_chart(parent,label)
 kind=record.get('kind')
 if kind=='I':
  if set(record)!={'kind'}or out['status']!='EMPTY':raise ValueError('Invalid interval/strict-guard exclusion')
  return 'EMPTY'
 if kind=='O':
  if set(record)!={'kind'}:raise ValueError('Invalid OPEN schema')
  if not allow_open:raise ValueError('Unpaid chart')
  return 'OPEN'
 if out['status']=='EMPTY':
  # A portable certificate must declare deterministic interval exclusions as I.
  raise ValueError('Use I for an interval-empty chart')
 if kind=='A':
  if set(record)!={'kind'}or safe_port(out['aux_image'])is None:raise ValueError('Unproved alpha-safe child')
  return 'SAFE'
 if kind not in('C','H'):raise ValueError('Unknown rule')
 m=exact_margin(out['aux_image'],label,record)
 if kind=='C' and m>=0:raise ValueError('Not a strict contradiction')
 if kind=='H' and m>0:raise ValueError('Not an alpha bound')
 return 'EMPTY'if kind=='C'else'SAFE'

def verify_cover(box,certificate, *, allow_open=False):
 b=normalize_box(box)
 if certificate.get('rule')!=RULE or certificate.get('rule_identity')!=rule_identity():raise ValueError('Rule/version identity mismatch')
 if certificate.get('box_sha256')!=box_hash(b):raise ValueError('Wrong original box ownership')
 if certificate.get('model_sha256')!=sha(paths.FROZEN/'models/B17_FULL.json'):raise ValueError('Wrong frozen B17 model')
 children=certificate.get('children')
 if not isinstance(children,dict)or set(children)!=set(GRAPH_LABELS):raise ValueError('Missing or extra canonical graph child')
 parent=parent_enclosure(b);counts={'EMPTY':0,'SAFE':0,'OPEN':0}
 for label in GRAPH_LABELS:
  outcome=verify_child(parent,label,children[label],allow_open=allow_open);counts[outcome]+=1
 if counts['OPEN'] and not allow_open:raise ValueError('Unpaid cover')
 return {'status':'PARTIAL_PREFIX_GRAPH_COVER'if counts['OPEN']else'COMPLETE_BOX_HIGH_EMPTY'if not counts['SAFE']else'COMPLETE_BOX_ALPHA_SAFE',
         'charts':len(GRAPH_LABELS),'empty_charts':counts['EMPTY'],'alpha_safe_charts':counts['SAFE'],'open_charts':counts['OPEN'],
         'whole_B_closed':False,'original_root_replayed':False,'macro_ledger':'14/15'}

if __name__=='__main__':
 import argparse
 a=argparse.ArgumentParser();a.add_argument('box');a.add_argument('certificate');a.add_argument('--allow-open',action='store_true');s=a.parse_args()
 b=json.loads(Path(s.box).read_text());b=b['box']if isinstance(b,dict)and'box'in b else b
 try:r=verify_cover(b,json.loads(Path(s.certificate).read_text()),allow_open=s.allow_open)
 except Exception as err:
  print(json.dumps({'status':'REJECTED','error':str(err)}));raise SystemExit(2)
 print(json.dumps(r,indent=2))
