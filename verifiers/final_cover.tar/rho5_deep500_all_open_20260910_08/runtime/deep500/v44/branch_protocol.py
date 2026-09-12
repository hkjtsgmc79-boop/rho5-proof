"""V44: full-source U41 prefix followed by an exact 24-coordinate cover.
No numerical optimizer is imported. A partial subtree never closes its parent.
The input to every split is reconstructed; stored auxiliary boxes are not trusted.
"""
from pathlib import Path
from collections import Counter
import json,hashlib
from v44_bootstrap import ROOT,FROZEN,source,db,vp,fs,Q,I
RULE='V44_POST_U41_FULL_IMAGE_BISECTION_DEPTH500_V1'

def json_hash(obj):
 return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()

def rule_hash():
 files={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in [ROOT/'v44_bootstrap.py',ROOT/'branch_protocol.py']}
 return json_hash({'rule':RULE,'files':files,'U41':vp.rule_identity()})

def binding(parent):
 box=source.inherited.validate_box(parent['box'])
 if fs.box_hash(box)!=parent['box_sha256']:raise ValueError('Invalid parent box hash')
 if type(parent['index']) is not int or parent['index']<0:raise ValueError('Invalid reported index')
 if not isinstance(parent['path'],str)or any(c not in '01' for c in parent['path']):raise ValueError('Invalid reported path')
 return {'rule':RULE,'rule_identity':rule_hash(),'model_sha256':vp.IDENTITY['b17_model_sha256'],'reported_round52_root_sha256':'4b72152fec20a58eff52ab6e93a8fd082fc85a28722d762412c0c5fc17abc707','parent_index':parent['index'],'reported_path':parent['path'],'box_sha256':parent['box_sha256'],'prefix_sha256':json_hash(parent['partial_certificate'])}

def prefix_image(parent,cross_check=True):
 # Same U41 schema/binding and the unmodified frozen trace acceptor. Return
 # its checked auxiliary image instead of discarding it and replaying twice.
 node=parent['partial_certificate'];box=source.inherited.validate_box(parent['box'])
 if not isinstance(node,dict)or node.get('kind')!='U41' or 'trace' not in node:
  raise ValueError('Expected an unconditional U41 prefix')
 if node!=vp.wrap(box,node['trace']):raise ValueError('Wrong U41 prefix identity/schema')
 result=db.replay_trace(box,node['trace'],cross_check=cross_check,allow_open=True)
 if result['status']!='OPEN' or result.get('aux_image') is None:
  raise ValueError('Expected an unpaid nonempty U41 prefix')
 out={'status':'BOUNDED','aux_image':result['aux_image']}
 return out,{k:v for k,v in result.items()if k!='aux_image'}

def wrap(parent,tree,profile):
 db.validate_profile(profile)
 return {**binding(parent),'profile':profile,'tree':tree}

def verify(parent,certificate,allow_open=False,cross_check=True):
 expect=binding(parent)
 if not isinstance(certificate,dict)or set(certificate)!=set(expect)|{'profile','tree'}:raise ValueError('Malformed V44 envelope')
 for k,v in expect.items():
  if certificate[k]!=v:raise ValueError('Wrong '+k)
 profile=certificate['profile'];db.validate_profile(profile)
 out,old=prefix_image(parent,cross_check)
 counts=Counter();margins=[]
 def walk(inbox,node,depth):
  if depth>500:raise ValueError('Excessive proof depth')
  if not isinstance(node,dict)or set(node)!={'waves','terminal'}:raise ValueError('Bad branch node')
  waves=node['waves']
  if not isinstance(waves,list) or len(waves)>128:raise ValueError('Bad node wave list')
  o=db.common_contract(inbox,profile=profile)
  for wave in waves:
   o=db.apply_wave(o,wave,profile=profile,cross_check=cross_check)
  counts['nodes']+=1;counts['maxdepth']=max(counts['maxdepth'],depth)
  counts['new_waves']+=len(waves);counts['new_bounds']+=sum(map(len,waves))
  t=node['terminal']
  if not isinstance(t,dict):raise ValueError('Missing terminal')
  kind=t.get('kind')
  if kind=='I':
   if set(t)!={'kind'} or o['status']!='EMPTY':raise ValueError('False interval terminal')
  elif kind=='O':
   if set(t)!={'kind'} or not allow_open:raise ValueError('Unpaid branch')
  else:
   if o['status']!='BOUNDED':raise ValueError('Only I may close a propagated contradiction')
   if kind=='A':
    if set(t)!={'kind'} or fs.safe_port(o['aux_image']) is None:raise ValueError('False inherited safe port')
   elif kind in ('C','H'):
    rows,boxes=db.rows_and_bounds(o['aux_image'],profile=profile)
    margin=source.inherited.dual_margin(rows,boxes,t)
    if cross_check:
     weights=dict(t['weights'])
     dense=[sum(Q(weights[j])*rows[j][0].get(i,Q(0)) for j in weights) for i in range(len(boxes))]
     rhs=sum(Q(w)*rows[j][1] for j,w in weights.items())
     if kind=='H':dense[23]-=t['objective_weight']
     independently=rhs-sum(dense[i]*(b.lo if dense[i]>=0 else b.hi) for i,b in enumerate(boxes))
     if kind=='H':independently-=t['objective_weight']*fs.ALPHA
     if independently!=margin:raise ValueError('Dense/sparse terminal disagreement')
    if (kind=='C' and margin>=0)or(kind=='H' and margin>0):raise ValueError('Failed exact dual terminal')
    margins.append(str(margin))
   elif kind=='S':
    if set(t)!={'kind','axis','left','right'}:raise ValueError('Incomplete bisection')
    ax=t['axis']
    if type(ax)is not int or not 0<=ax<24:raise ValueError('Split must be an actual image coordinate')
    b=[list(z)for z in o['aux_image']];lo,hi=map(Q,b[ax]);mid=(lo+hi)/2
    if not lo<mid<hi:raise ValueError('Degenerate bisection')
    left=[list(z)for z in b];right=[list(z)for z in b];left[ax][1]=str(mid);right[ax][0]=str(mid)
    walk({'status':'BOUNDED','aux_image':left},t['left'],depth+1)
    walk({'status':'BOUNDED','aux_image':right},t['right'],depth+1)
   else:raise ValueError('Unknown branch terminal')
  counts[kind]+=1
 walk(out,certificate['tree'],0)
 if counts['nodes']!=2*counts['S']+1:raise ValueError('Incomplete binary cover')
 if counts['I']+counts['C']+counts['H']+counts['A']+counts['O']!=counts['S']+1:raise ValueError('Leaf count mismatch')
 return {'status':'OPEN'if counts['O']else'SAFE'if(counts['A']+counts['H'])else'EMPTY','index':parent['index'],'sample':parent.get('sample'),'prior_waves':old['waves'],'prior_bounds':old['bounds'],'counts':dict(counts),'margins_sha256':json_hash(margins),'unreceived_Round52_full_tree_replayed_here':False}

if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('parent',type=Path);ap.add_argument('certificate',type=Path);ap.add_argument('--allow-open',action='store_true');a=ap.parse_args()
 try:r=verify(json.loads(a.parent.read_text()),json.loads(a.certificate.read_text()),a.allow_open)
 except Exception as e:print(json.dumps({'status':'REJECTED','error':str(e)}));raise SystemExit(2)
 print(json.dumps(r,ensure_ascii=False,indent=2))
