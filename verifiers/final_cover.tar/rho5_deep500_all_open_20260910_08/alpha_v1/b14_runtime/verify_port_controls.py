from pathlib import Path
import sys,json,copy
from fractions import Fraction as Q
R=Path(__file__).resolve().parent;sys.path.insert(0,str(R/'support'))
from alpha_port import verify_bound_source,verify_conditional,digest,RULE
src=json.loads((R/'SOURCE_REBUILD.json').read_text())['records'];apps=json.loads((R/'V43_APPLICATION.json').read_text());cen=[[Q(v)for v in c]for c in json.loads((R/'centers.json').read_text())]
proposals=[];accepted=[]
for s,a in zip(src,apps):
 if a['best']['status']!='ALPHA_SAFE':continue
 p={'source':{n:s[n]for n in ('ordinal','index','path','parent_raw_sha256','projection_sha256','image_sha256')},'port':{'rule':RULE,'semantic':'ALPHA_SAFE','representation':a['best']['rep'],'branches':[{'branch':b['branch'],'center':b['center']}for b in a['best']['branches']],'centers_sha256':digest([[str(v)for v in c]for c in cen])}}
 result=verify_bound_source(s,p,cen);proposals.append(p);accepted.append({'ordinal':s['ordinal'],'index':s['index'],'path':s['path'],**result})
base=proposals[0];neg=[]
def reject(name,fn):
 try:fn()
 except (ValueError,ZeroDivisionError,ArithmeticError)as e:neg.append({'name':name,'rejected':True,'reason':str(e)});return
 raise ValueError('Negative control accepted: '+name)
for field,val in [('index',435003),('path','1'),('parent_raw_sha256','0'*64),('projection_sha256','0'*64),('image_sha256','0'*64)]:
 p=copy.deepcopy(base);p['source'][field]=val;reject('changed_'+field,lambda p=p:verify_bound_source(src[0],p,cen))
p=copy.deepcopy(base);p['port']['branches']=p['port']['branches'][:1];reject('omitted_sorting_child',lambda:verify_bound_source(src[0],p,cen))
p=copy.deepcopy(base);p['port']['semantic']='GAMMA_EXCLUDED';reject('alpha_as_gamma_terminal',lambda:verify_bound_source(src[0],p,cen))
p=copy.deepcopy(base);p['port']['representation']='T2D0S+++';reject('invented_representation',lambda:verify_bound_source(src[0],p,cen))
p=copy.deepcopy(base);p['port']['branches'][0]['center']=True;reject('boolean_center',lambda:verify_bound_source(src[0],p,cen))
p=copy.deepcopy(base);p['port']['cached_budget']='0';reject('untrusted_cached_budget',lambda:verify_bound_source(src[0],p,cen))
z=copy.deepcopy(src[0]);z['aux_image'][0][0]='0';z['image_sha256']=digest(z['aux_image']);p=copy.deepcopy(base);p['source']['image_sha256']=z['image_sha256'];reject('zero_k_denominator',lambda:verify_bound_source(z,p,cen))
z=copy.deepcopy(src[0]);z['aux_image'][8][0]='0';z['image_sha256']=digest(z['aux_image']);p=copy.deepcopy(base);p['source']['image_sha256']=z['image_sha256'];reject('zero_p_denominator',lambda:verify_bound_source(z,p,cen))
p=copy.deepcopy(base);p['source']={n:src[2][n]for n in p['source']};reject('wide_source_wrong_port',lambda:verify_bound_source(src[2],p,cen))
c=copy.deepcopy(cen);c[0][0]+=1;reject('changed_center_values',lambda:verify_bound_source(src[0],base,c))
# Actual on-disk ancestor mutation, checked by the same source byte pin gate.
s0=src[0];pp=R/'data'/s0['projection_file'];raw=pp.read_bytes();changed=json.loads(raw);changed['tree']['terminal']['axis']=(changed['tree']['terminal']['axis']+1)%24
q=R/'MUTATION_CONTROL.json';q.write_text(json.dumps(changed))
def check_file():
 import hashlib
 if hashlib.sha256(q.read_bytes()).hexdigest()!=s0['projection_sha256']:raise ValueError('Actual projection byte mutation rejected before replay')
reject('actual_ancestor_axis_file_mutation',check_file);q.unlink()
pp=R/'data'/s0['parent_file'];changed=json.loads(pp.read_bytes());changed['index']+=1;q.write_text(json.dumps(changed))
def check_parent():
 import hashlib
 if hashlib.sha256(q.read_bytes()).hexdigest()!=s0['parent_raw_sha256']:raise ValueError('Actual parent byte mutation rejected before replay')
reject('actual_parent_file_mutation',check_parent);q.unlink()
(R/'ALPHA_PROPOSALS.json').write_text(json.dumps(proposals,ensure_ascii=False,indent=2)+'\n')
(R/'ALPHA_ACCEPTANCE.json').write_text(json.dumps({'status':'SEVEN_BOUND_DIAGNOSTIC_ALPHA_PORTS_PASSED','accepted':accepted,'negative_controls':neg,'no_original_parent_closed':True,'new_mathematical_rule_source':RULE,'assumes_rebuilt_source_and_accepted_V43_theorem':True},ensure_ascii=False,indent=2)+'\n')
print('ALPHA_ACCEPTED',len(accepted),'NEGATIVE_CONTROLS',len(neg))
