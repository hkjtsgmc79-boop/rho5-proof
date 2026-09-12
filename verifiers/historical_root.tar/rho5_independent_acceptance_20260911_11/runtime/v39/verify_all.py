#!/usr/bin/env python3
"""Default audit: exact acceptance only, no LP and no large-tree search."""
import json,hashlib,time,sys
from pathlib import Path
from collections import Counter
if not __debug__:raise RuntimeError('Run without -O: source control assertions are part of this audit')
ROOT=Path(__file__).resolve().parent

def check_manifest():
 p=ROOT/'MANIFEST.json'
 if not p.is_file():raise ValueError('Missing static delivery manifest')
 data=json.loads(p.read_text())
 for name,h in data['sha256'].items():
  path=ROOT/name
  if not path.is_file()or hashlib.sha256(path.read_bytes()).hexdigest()!=h:raise ValueError('Delivery hash mismatch: '+name)
 return len(data['sha256'])

def main():
 start=time.monotonic();h=check_manifest()
 from verify_input import run as audit
 from verify_math import run as math
 from verify_controls import run as controls
 from verify_negative import run as negative
 from graph_protocol import verify_cover,parent_enclosure,paths
 from envelope import verify as env_verify
 from interval_capacity import root_box
 from tree_protocol import halve
 import ablation
 from relaxation import margin
 ia=audit();ma=math();co=controls();ne=negative()
 print(json.dumps({'input':ia,'math_summary':{k:v for k,v in ma.items()if k!='boundary_controls'},'physical_controls':co,'negative':ne},ensure_ascii=False),flush=True)
 samples=json.loads((ROOT/'inputs/diagnostics/audit_final/SAMPLE_CONTROLS.json').read_text());counts=Counter();chart=Counter();closed=[];widths=[b.hi-b.lo for b in root_box()]
 for item in samples:
  i=item['sample'];b=root_box()
  for bit in item['path']:
   axis=max(range(17),key=lambda j:(b[j].hi-b[j].lo)/widths[j]);b=halve(b,axis)[int(bit)]
  if [v.data()for v in b]!=item['box']:raise ValueError('Sample original path mismatch')
  if parent_enclosure(item['box'])['aux_image']!=item['oracle']['aux_image']:raise ValueError('Frozen high_value_v1 enclosure mismatch')
  cert=json.loads((ROOT/f'evidence/frontier_covers/sample_{i:02d}.json').read_text())
  result=verify_cover(b,cert,allow_open=True);counts[result['status']]+=1
  chart.update(rec['kind']for rec in cert['children'].values())
  if result['open_charts']==0:closed.append(i)
 assert closed==[0,22,28,34,39,48,50,52,57,58]
 assert chart==Counter({'I':11406,'C':310,'O':380})
 print(json.dumps({'sample_box_outcomes':dict(counts),'chart_outcomes':dict(chart)},ensure_ascii=False),flush=True)
 envelope=env_verify(json.loads((ROOT/'evidence/new_boxes_root_envelope.json').read_text()),allow_open=True)
 # Recompute every accepted ablation component, without running discovery.
 ad=json.loads((ROOT/'evidence/ablation.json').read_text());baseclosed=[]
 for r in ad['records']:
  if r['kind']=='UNRESOLVED':continue
  out=ablation.baseline_contract(parent_enclosure(samples[r['sample']]['box']))
  if r['kind']=='INTERVAL':assert out['status']=='EMPTY'
  else:
   assert out['status']=='BOUNDED';m=margin(out['aux_image'],r['certificate']);assert m<0 if r['kind']=='C'else m<=0
  baseclosed.append(r['sample'])
 assert baseclosed==[22,34,39,48,50,52,57,58]
 result={'status':'V39_PREFIX_MAX_GRAPH_AND_TEN_BOX_CERTIFICATES_PASS_NOT_GLOBAL_CLOSURE','seconds':time.monotonic()-start,
  'static_files_checked':h,'math_summary':{k:v for k,v in ma.items()if k!='boundary_controls'},'input_audit':ia,'physical_controls':co,'negative_tests':ne,
  'samples_replayed':64,'closed_boxes':10,'remaining_sample_boxes':54,'strictly_new_over_same_contraction_ablation':[0,28],
  'chart_outcomes':dict(chart),'small_original_root_envelope':envelope,'unreceived_round48_large_tree_replayed_here':False,
  'whole_B_closed':False,'macro_ledger':'14/15'}
 print(json.dumps(result,ensure_ascii=False,separators=(',',':')),flush=True)
if __name__=='__main__':main()
