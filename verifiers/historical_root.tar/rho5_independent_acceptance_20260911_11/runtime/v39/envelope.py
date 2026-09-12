#!/usr/bin/env python3
"""Small original-root envelope for the ten new complete box certificates.
It deliberately keeps every unpaid sibling OPEN. Not the unreceived Round48 tree.
"""
import json
from pathlib import Path
from graph_protocol import *
from interval_capacity import root_box
from tree_protocol import halve

def build():
 d=json.loads((paths.ROOT/'evidence/frontier_diagnostics.json').read_text())
 good={r['source_path']:r['sample']for r in d['records']if r['classification']['open_charts']==0}
 widths=[b.hi-b.lo for b in root_box()];records=[]
 def walk(route,b):
  if route in good:records.append({'kind':'G','sample':good[route]});return
  if not any(p.startswith(route)for p in good):records.append({'kind':'O'});return
  axis=max(range(17),key=lambda i:(b[i].hi-b[i].lo)/widths[i]);records.append({'kind':'S','axis':axis})
  l,r=halve(b,axis);walk(route+'0',l);walk(route+'1',r)
 walk('',root_box())
 return {'model_sha256':sha(paths.FROZEN/'models/B17_FULL.json'),'rule_identity':rule_identity(),'nodes':records,'original_round48_tree_received':False}

def verify(data,allow_open=False):
 if data.get('model_sha256')!=sha(paths.FROZEN/'models/B17_FULL.json')or data.get('rule_identity')!=rule_identity():raise ValueError('envelope identity mismatch')
 nodes=data['nodes'];stack=[(root_box(),'')];pos=0;counts={'nodes':0,'splits':0,'new_proved_boxes':0,'open':0};samples=json.loads((paths.ROOT/'inputs/diagnostics/audit_final/SAMPLE_CONTROLS.json').read_text())
 while stack:
  b,route=stack.pop()
  if pos>=len(nodes):raise ValueError('truncated envelope')
  rec=nodes[pos];pos+=1;counts['nodes']+=1
  if rec['kind']=='S':
   if set(rec)!={'kind','axis'}:raise ValueError('bad split')
   l,r=halve(b,rec['axis']);stack.extend([(r,route+'1'),(l,route+'0')]);counts['splits']+=1
  elif rec['kind']=='O':
   if set(rec)!={'kind'}:raise ValueError('bad OPEN')
   counts['open']+=1
  elif rec['kind']=='G':
   if set(rec)!={'kind','sample'}or type(rec['sample'])is not int or not 0<=rec['sample']<64:raise ValueError('bad G')
   n=rec['sample'];inp=samples[n]
   if inp['sample']!=n or inp['path']!=route or inp['box']!=[z.data()for z in b]:raise ValueError('wrong exact root route')
   cert=json.loads((paths.ROOT/f'evidence/frontier_covers/sample_{n:02d}.json').read_text())
   out=verify_cover(b,cert)
   if out['open_charts']:raise ValueError('open G child')
   counts['new_proved_boxes']+=1
  else:raise ValueError('unknown envelope terminal')
 if pos!=len(nodes):raise ValueError('unvisited records')
 assert counts['nodes']==2*counts['splits']+1
 if counts['open']and not allow_open:raise ValueError('Unpaid siblings remain')
 return {**counts,'status':'ORIGINAL_ROOT_ENVELOPE_PARTIAL','not_the_round48_tree':True,'whole_B_closed':False}

if __name__=='__main__':
 import argparse
 a=argparse.ArgumentParser();a.add_argument('--build',action='store_true');a.add_argument('--allow-open',action='store_true');args=a.parse_args()
 target=paths.ROOT/'evidence/new_boxes_root_envelope.json'
 if args.build:target.write_text(json.dumps(build(),separators=(',',':'))+'\n')
 out=verify(json.loads(target.read_text()),allow_open=args.allow_open)
 print(json.dumps(out,indent=2))
