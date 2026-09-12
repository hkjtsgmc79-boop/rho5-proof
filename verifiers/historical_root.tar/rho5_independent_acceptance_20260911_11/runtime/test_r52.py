"""Integration boundaries for old U41 and explicitly versioned C42 acceptance."""
from pathlib import Path
import copy,json
import r52_protocol as p
ROOT=Path(__file__).resolve().parent
def read(f):return json.loads((ROOT/f).read_text())
samples=read('inherited/ROUND51_SAMPLES64.json');checks=[]
def reject(name,fn):
 try:fn()
 except (ValueError,AssertionError,TypeError,KeyError):checks.append(name);return
 raise AssertionError('Accepted invalid case: '+name)
node=read('v42/certificates/closed_21.json');box=samples[21]['box']
assert p.verify_leaf(box,node,'native')==p.verify_leaf(box,node,'fraction')=='EMPTY'
old=p.old.binding();assert old['v41_rule_identity']=='9f31a41c08071a6555fa4da3b13d73cedcb0e6b635185855bf0464ca16773aa6'
partial=read('v42/certificates/composed_20.json');box=samples[20]['box']
bind=p.v42.binding(box,partial['prefix'])
assert all(partial[k]==v for k,v in bind.items())
val=p.v42.verify(box,partial,True,True);assert val['children']=={'EMPTY':187,'SAFE_ALPHA':0,'OPEN':2}
reject('partial C42 cannot close a root',lambda:p.verify_leaf(box,partial))
bad=copy.deepcopy(partial);bad['rule_identity']='0'*64
reject('wrong C42 identity',lambda:p.verify_leaf(box,bad))
badbox=copy.deepcopy(box);badbox[0][0]=badbox[0][1]
reject('wrong actual parent box',lambda:p.verify_leaf(badbox,partial))
bad=copy.deepcopy(partial);bad['aux_image']=[]
reject('cached image injection',lambda:p.verify_leaf(box,bad))
reject('old reader cannot accept C42',lambda:p.old.verify_leaf(box,partial))
envelope={'model_sha256':p.sha(p.tp.MODEL),'root_path':'','nodes':[{'kind':'O'}]}
for label,change in [('root_path',{'root_path':'1'}),('model',{'model_sha256':'0'*64}),('task',{'task':'other'})]:
 reject('wrong root '+label,lambda change=change:p.structure(envelope|change))
positive=[]
for f in (ROOT/'condition_probe').glob('result_*.json'):
 r=json.loads(f.read_text())
 if r['status']=='OPEN':continue
 assert p.verify_leaf(r['box'],r['node'],'native')==r['status'];positive.append(r['index'])
assert p.old.binding()==old
print(json.dumps({'status':'R52_INTEGRATION_BOUNDARIES_PASS','negative_controls':checks,'negative_count':len(checks),'unchanged_U41_sparse_dense_PASS':True,'C42_partial_counts':val['children'],'new_complete_C42_positive_controls':positive,'binding':p.binding()},indent=2))
