"""Exact V40 proof checker. All 189 canonical prefix graphs must be paid.
The 64 supplied boxes are NOT the complete B17 root. OPEN is never success.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json
import bootstrap
from combined import *
from sharp_prefix import contract_sharp
from linear_certificate import dual_margin
RULE='V40_SAME_SOURCE_PROJECTIVE_COVER_V1'
FILES=('bootstrap.py','full_source.py','projective_graph.py','sharp_prefix.py','homogeneous.py','combined.py','linear_certificate.py','protocol.py')

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def rule_identity():
 d={n:sha(bootstrap.ROOT/n)for n in FILES}
 d['received_light_zip']=bootstrap.ARCHIVE_SHA
 return hashlib.sha256(json.dumps(d,sort_keys=True,separators=(',',':')).encode()).hexdigest()
MODEL_SHA=sha(bootstrap.RECEIVED/'models/B17_FULL.json')
REPORTED_ROOT_SHA='724b10b0eabf3cdee676d6bcbff99d72269b6a6fb1fdddca7446a05badd03701'
MODEL=json.loads((bootstrap.RECEIVED/'models/B17_FULL.json').read_text())

def validate_box(box):
 if not isinstance(box,(list,tuple))or len(box)!=17:raise ValueError('17 actual frame intervals required')
 out=[]
 for i,pair in enumerate(box):
  if not isinstance(pair,(list,tuple))or len(pair)!=2:raise ValueError('bad interval')
  if any(isinstance(x,(bool,float))or not isinstance(x,(str,int,Q))for x in pair):raise ValueError('Exact rational endpoints only')
  lo,hi=map(Q,pair);rl,rh=map(Q,MODEL['bounds'][MODEL['frame_order'][i]])
  if not rl<=lo<=hi<=rh:raise ValueError('Box outside frozen original root')
  out.append([str(lo),str(hi)])
 return out

MODES={'FULL':contract_full,'QUOTIENT':contract_sharp,'PROJECTED':contract_projective,'HOMOGENEOUS':contract_homogeneous,'COMBINED':contract_combined}

def verify_child_new(parent,label,record,allow_open=False):
 if label not in GRAPH_LABELS or not isinstance(record,dict):raise ValueError('unknown graph or record')
 mode=record.get('mode');proof=record.get('proof')
 if mode=='OPEN':
  if record!={'mode':'OPEN','proof':{'kind':'O'}}:raise ValueError('Bad OPEN schema')
  if not allow_open:raise ValueError('Unpaid conditional graph')
  return 'OPEN'
 if mode not in MODES or not isinstance(proof,dict):raise ValueError('Unknown V40 mode')
 expected={'mode','proof'}
 if mode in ('HOMOGENEOUS','COMBINED')and proof.get('kind')in('C','H'):expected.add('sources')
 if set(record)!=expected:raise ValueError('Child schema mismatch')
 z=MODES[mode](parent,label);kind=proof.get('kind')
 if kind=='I':
  if proof!={'kind':'I'}or z['status']!='EMPTY':raise ValueError('False interval exclusion')
  return 'EMPTY'
 if z['status']=='EMPTY':raise ValueError('Use deterministic I proof')
 if kind=='A':
  if proof!={'kind':'A'}or safe_port(z['aux_image'])is None:raise ValueError('False alpha port')
  return 'SAFE'
 if kind not in('C','H'):raise ValueError('Unknown leaf')
 if mode in ('FULL','QUOTIENT'):rows,boxes=rows_for(z['aux_image'],label)
 elif mode=='PROJECTED':rows,boxes=extended_rows(z['aux_image'],label)
 else:rows,boxes=generalized_rows(z['aux_image'],label,record['sources'])
 margin=dual_margin(rows,boxes,proof)
 if kind=='C'and margin>=0:raise ValueError('Not an exact contradiction')
 if kind=='H'and margin>0:raise ValueError('Not an exact alpha bound')
 return 'EMPTY'if kind=='C'else'SAFE'

def verify_parent(box,cert,allow_open=False):
 b=validate_box(box)
 if cert.get('rule')!=RULE or cert.get('rule_identity')!=rule_identity():raise ValueError('Wrong V40 rule identity')
 if cert.get('model_sha256')!=MODEL_SHA:raise ValueError('Wrong original model')
 if cert.get('reported_root_sha256')!=REPORTED_ROOT_SHA:raise ValueError('Wrong declared R49 root')
 if cert.get('box_sha256')!=box_hash(b):raise ValueError('Wrong actual box')
 if set(cert.get('children',{}))!=set(GRAPH_LABELS):raise ValueError('Missing/extra prefix alternative')
 parent=parent_enclosure(b);counts={'EMPTY':0,'SAFE':0,'OPEN':0};modes={};kinds={}
 for lab in GRAPH_LABELS:
  rec=cert['children'][lab];res=verify_child_new(parent,lab,rec,allow_open);counts[res]+=1
  modes[rec['mode']]=modes.get(rec['mode'],0)+1;k=rec['proof']['kind'];kinds[k]=kinds.get(k,0)+1
 if counts['OPEN']and not allow_open:raise ValueError('Not a complete parent proof')
 return {'status':'PARTIAL_BOX_COVER'if counts['OPEN']else'COMPLETE_BOX_HIGH_EMPTY'if not counts['SAFE']else'COMPLETE_BOX_ALPHA_SAFE',
         'sample_ordinal':cert.get('sample_ordinal'),'reported_index':cert.get('reported_index'),
         'children':counts,'modes':modes,'kinds':kinds,'whole_B_closed':False,
         'original_full_tree_replayed':False,'ancestry_beyond_box_hash_verified_here':False,'macro_ledger':'14/15'}

if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('box');ap.add_argument('certificate');ap.add_argument('--allow-open',action='store_true');args=ap.parse_args()
 b=json.loads(Path(args.box).read_text());b=b.get('box',b)if isinstance(b,dict)else b
 try:r=verify_parent(b,json.loads(Path(args.certificate).read_text()),args.allow_open)
 except Exception as err:print(json.dumps({'status':'REJECTED','error':str(err)}));raise SystemExit(2)
 print(json.dumps(r,indent=2))
