"""Fault injection into the new wrapper; valid proofs are independently replayed elsewhere."""
from pathlib import Path
from copy import deepcopy
import json
from branch_protocol import verify,wrap
ROOT=Path(__file__).resolve().parent

def first_c(tree):
 t=tree['terminal']
 if t['kind']=='C':return t
 if t['kind']=='S':return first_c(t['left'])or first_c(t['right'])
 return None

def run():
 table=json.loads((ROOT/'INSERTION_INDEX.json').read_text())
 item=min((x for x in table['parents']if x['complete']),key=lambda x:x['counts']['nodes'])
 parent=json.loads((ROOT/item['parent_file']).read_text());cert=json.loads((ROOT/item['certificate_file']).read_text())
 tests=[]
 def add(name,fn,on_parent=False):
  p=deepcopy(parent);c=deepcopy(cert);fn(p if on_parent else c);tests.append((name,p,c))
 add('wrong_rule',lambda c:c.__setitem__('rule','OLD_C'))
 add('wrong_rule_hash',lambda c:c.__setitem__('rule_identity','0'*64))
 add('wrong_model',lambda c:c.__setitem__('model_sha256','0'*64))
 add('wrong_R52_root',lambda c:c.__setitem__('reported_round52_root_sha256','0'*64))
 add('wrong_parent_index',lambda c:c.__setitem__('parent_index',c['parent_index']+1))
 add('wrong_parent_path',lambda c:c.__setitem__('reported_path',c['reported_path']+'0'))
 add('wrong_parent_box',lambda c:c.__setitem__('box_sha256','0'*64))
 add('wrong_U41_prefix_hash',lambda c:c.__setitem__('prefix_sha256','0'*64))
 add('untrusted_cached_aux_box',lambda c:c.__setitem__('aux_image',[]))
 add('unknown_profile',lambda c:c.__setitem__('profile','MAGIC'))
 add('truncated_tree_missing_child',lambda c:c['tree']['terminal'].pop('right'))
 add('split_in_product_column',lambda c:c['tree']['terminal'].__setitem__('axis',24))
 add('boolean_split_axis',lambda c:c['tree']['terminal'].__setitem__('axis',True))
 add('root_false_interval_leaf',lambda c:c.__setitem__('tree',{'waves':[],'terminal':{'kind':'I'}}))
 add('root_unpaid_leaf',lambda c:c.__setitem__('tree',{'waves':[],'terminal':{'kind':'O'}}))
 add('root_false_alpha_port',lambda c:c.__setitem__('tree',{'waves':[],'terminal':{'kind':'A'}}))
 add('unrecognized_safe_leaf',lambda c:c.__setitem__('tree',{'waves':[],'terminal':{'kind':'ASSUME_SAFE'}}))
 add('zero_dual_weight',lambda c:first_c(c['tree'])['weights'][0].__setitem__(1,0))
 add('negative_dual_weight',lambda c:first_c(c['tree'])['weights'][0].__setitem__(1,-1))
 add('boolean_dual_weight',lambda c:first_c(c['tree'])['weights'][0].__setitem__(1,True))
 add('duplicate_dual_row',lambda c:first_c(c['tree'])['weights'].append(deepcopy(first_c(c['tree'])['weights'][0])))
 add('illegal_dual_row',lambda c:first_c(c['tree'])['weights'][0].__setitem__(0,10**9))
 add('empty_dual_support',lambda c:first_c(c['tree']).__setitem__('weights',[]))
 add('changed_U41_prefix',lambda p:p['partial_certificate']['trace']['waves'][0][0].__setitem__('objective_weight',0),True)
 add('extra_node_cached_box',lambda c:c['tree'].__setitem__('cached_box',[]))
 # Rebind the outer wrapper after corrupting a bound so this control reaches
 # the old exact mathematical checker rather than stopping at the outer hash.
 badp=deepcopy(parent)
 badp['partial_certificate']['trace']['waves'][0][0]['objective_weight']=0
 tests.append(('zero_bound_multiplier_after_outer_rebinding',badp,wrap(badp,deepcopy(cert['tree']),cert['profile'])))
 outcomes=[]
 for name,p,c in tests:
  try:verify(p,c,allow_open=False,cross_check=True)
  except (ValueError,AssertionError,KeyError,TypeError)as e:outcomes.append({'name':name,'rejected':True,'reason':str(e)})
  else:raise ValueError('Malformed proof accepted: '+name)
 # OPEN may only be retained with explicit partial-check mode; it never closes its parent.
 partial=wrap(parent,{'waves':[],'terminal':{'kind':'O'}},cert['profile'])
 r=verify(parent,partial,allow_open=True,cross_check=True)
 if r['status']!='OPEN' or r['counts'].get('O')!=1:raise ValueError('Partial check converted OPEN to success')
 from controller_adapter import verify_at_actual_leaf
 badbox=deepcopy(parent['box']);badbox[0][0]=str(__import__('fractions').Fraction(badbox[0][0])-1)
 for name,box,index,path in [
  ('wrong_actual_leaf_box',badbox,parent['index'],parent['path']),
  ('wrong_actual_leaf_index',parent['box'],parent['index']+1,parent['path']),
  ('wrong_actual_leaf_path',parent['box'],parent['index'],parent['path']+'0')]:
  try:verify_at_actual_leaf(box,index,path,parent,cert)
  except ValueError as e:outcomes.append({'name':name,'rejected':True,'reason':str(e)})
  else:raise ValueError('Wrong controller leaf accepted')
 return {'rejection_controls':len(outcomes),'explicit_partial_status_preserved':True,'outcomes':outcomes}
if __name__=='__main__':print(json.dumps(run(),ensure_ascii=False,indent=2))
