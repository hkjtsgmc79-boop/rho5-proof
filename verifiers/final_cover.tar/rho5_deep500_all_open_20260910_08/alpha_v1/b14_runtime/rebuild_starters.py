from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
import json,sys,hashlib,time
ROOT=Path(__file__).resolve().parent
D=ROOT/'data';IN=ROOT/'input'
sys.dont_write_bytecode=True
sys.path.insert(0,str(D/'deep'))
import deep_math as dm
bp=dm.load_protocol(D/'deep')
mani=json.loads((D/'deep/runtime/DEEP500_MANIFEST.json').read_text())
starters=json.loads((IN/'STARTER_CASES.json').read_text())['cases']
parents={}
for p in D.rglob('parent*.json'):
 try:
  a=json.loads(p.read_text())
  if not isinstance(a,dict) or 'partial_certificate' not in a:continue
  key=(a['index'],bp.json_hash(a['partial_certificate']),a['box_sha256'])
  parents[key]=(p,a)
 except (ValueError,KeyError):pass
prefix_cache={};node_cache={};records=[];count=Counter();t0=time.monotonic()
for ordinal,c in enumerate(starters):
 p=D/c['projection_file']; raw=p.read_bytes()
 if dm.file_sha(p)!=c['projection_raw_sha256']:raise ValueError('projection byte mismatch')
 cert=json.loads(raw);parent_path,parent=parents[(c['index'],cert['prefix_sha256'],cert['box_sha256'])]
 if cert['rule']==dm.OLD_RULE:
  dm.validate_legacy_binding(parent,cert,mani['legacy_rule_identity'],bp)
 else:
  expect=bp.binding(parent)
  if {k:cert[k] for k in expect}!=expect:raise ValueError('bad deep binding')
  dm.counts(cert['tree'])
 key=bp.json_hash(parent)
 if key not in prefix_cache:
  prefix_cache[key]=bp.prefix_image(parent,cross_check=True)
  count['prefixes']+=1; count['prefix_waves']+=prefix_cache[key][1]['waves']; count['prefix_bounds']+=prefix_cache[key][1]['bounds']
 o,old=prefix_cache[key];node=cert['tree'];visited=[]
 for depth in range(len(c['path'])+1):
  state_key=bp.json_hash({'in':o,'waves':node['waves'],'profile':cert['profile']})
  if state_key not in node_cache:
   oo=bp.db.common_contract(o,profile=cert['profile'])
   for wave in node['waves']:oo=bp.db.apply_wave(oo,wave,profile=cert['profile'],cross_check=True)
   node_cache[state_key]=oo
   count['visited_unique_nodes']+=1; count['local_waves']+=len(node['waves']);count['local_bounds']+=sum(map(len,node['waves']))
  o=node_cache[state_key]
  if o['status']!='BOUNDED':raise ValueError('unanticipated contracted empty source')
  term=node['terminal'];visited.append({'depth':depth,'wave_sha256':bp.json_hash(node['waves']),'terminal_kind':term['kind'],'axis':term.get('axis'),'image_sha256':bp.json_hash(o['aux_image'])})
  if depth==len(c['path']):
   if term!={'kind':'O'}:raise ValueError('not diagnostic O')
   break
  if term['kind']!='S' or type(term['axis'])!=int or not 0<=term['axis']<24:raise ValueError('bad split')
  ax=term['axis'];b=[list(v)for v in o['aux_image']];lo,hi=map(Q,b[ax]);mid=(lo+hi)/2
  if not lo<mid<hi:raise ValueError('degenerate split')
  branch=c['path'][depth]
  if branch=='0':b[ax][1]=str(mid);node=term['left']
  else:b[ax][0]=str(mid);node=term['right']
  o={'status':'BOUNDED','aux_image':b}
 record={'ordinal':ordinal,'index':c['index'],'path':c['path'],'absolute_depth':c['absolute_depth'],'projection_file':c['projection_file'],'projection_sha256':c['projection_raw_sha256'],'parent_file':str(parent_path.relative_to(D)),'parent_raw_sha256':dm.file_sha(parent_path),'parent_binding':bp.binding(parent),'source_scope':c['source_scope'],'aux_image':o['aux_image'],'image_sha256':bp.json_hash(o['aux_image']),'visited':visited,'counts_prior':{k:v for k,v in old.items() if k!='aux_image'}}
 records.append(record)
 out={'status':'STARTER_PATHS_REBUILT_NOT_PARENT_CLOSURE','rule':bp.RULE,'rule_identity':bp.rule_hash(),'counts':dict(count),'records':records}
 (ROOT/'SOURCE_REBUILD.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
 print('DONE',ordinal,c['index'],c['absolute_depth'], 'sec',round(time.monotonic()-t0,2),dict(count),flush=True)
print('COMPLETE',len(records),flush=True)
