"""Adversarial exact checks. Rejection is part of the public proof protocol."""
import copy,json
from fractions import Fraction as Q
from protocol import *
from capacity import capacity

def run():
 tests=[]
 def reject(name,fn):
  try:fn()
  except (ValueError,AssertionError,KeyError,IndexError,TypeError,ZeroDivisionError):tests.append(name);return
  raise AssertionError('Invalid input accepted: '+name)
 cert=json.loads((bootstrap.ROOT/'evidence/parents/sample_00.json').read_text());box=cert['box']
 def edited(field,val):
  c=copy.deepcopy(cert);c[field]=val;return c
 for field in ('rule_identity','model_sha256','reported_root_sha256','box_sha256'):
  reject('wrong_'+field,lambda field=field:verify_parent(box,edited(field,'0'*64)))
 c=copy.deepcopy(cert);c['children'].pop(next(iter(c['children'])))
 reject('missing_prefix_alternative',lambda:verify_parent(box,c))
 c=copy.deepcopy(cert);c['children']['NONEXISTENT']={'mode':'OPEN','proof':{'kind':'O'}}
 reject('extra_prefix_alternative',lambda:verify_parent(box,c))
 reject('floating_box_endpoint',lambda:validate_box([[1.0,2.0]]*17))
 reject('boolean_box_endpoint',lambda:validate_box([[True,True]]*17))
 b=copy.deepcopy(box);b[0]=['0','1']
 reject('box_outside_original_root',lambda:validate_box(b))
 parent=parent_enclosure(box);lab=GRAPH_LABELS[0]
 reject('unpaid_graph_in_strict_mode',lambda:verify_child_new(parent,lab,{'mode':'OPEN','proof':{'kind':'O'}}))
 reject('unknown_acceptance_mode',lambda:verify_child_new(parent,lab,{'mode':'FAKE','proof':{'kind':'I'}}))
 reject('unknown_graph_label',lambda:verify_child_new(parent,'bad',{'mode':'FULL','proof':{'kind':'I'}}))
 # On a true gamma-high canonical matrix, no interval contradiction is possible.
 source=json.loads((bootstrap.V39/'inputs/evidence/capacity_controls.json').read_text())[0]
 f=list(map(Q,source['maximum']['frame']))
 if f[8]<0:f=f[:5]+[-v for v in f[5:]]
 out=capacity(f);u,x,v,q=[f[j:j+3]for j in(5,8,11,14)]
 lab=exact_labels(u,x,v,q,*[out['prefix'][n]for n in('beta','p','e')])[0]
 point_parent=parent_enclosure([[str(z),str(z)]for z in f])
 reject('false_interval_empty_at_physical_point',lambda:verify_child_new(point_parent,lab,{'mode':'FULL','proof':{'kind':'I'}}))
 # Validate exact dual schemas independently of the discovery process.
 rows=[({0:Q(1)},Q(1)),({0:Q(-1)},Q(0))];bounds=[I(0,1)]
 for name,rec in (
  ('empty_weights',{'kind':'C','weights':[]}),
  ('zero_weight',{'kind':'C','weights':[[0,0]]}),
  ('negative_weight',{'kind':'C','weights':[[0,-1]]}),
  ('boolean_weight',{'kind':'C','weights':[[0,True]]}),
  ('duplicate_row',{'kind':'C','weights':[[0,1],[0,1]]}),
  ('invalid_row',{'kind':'C','weights':[[2,1]]}),
  ('float_weight',{'kind':'C','weights':[[0,1.5]]}),
  ('nonpositive_height_weight',{'kind':'H','weights':[[0,1]],'objective_weight':0}),
  ('forged_height_target',{'kind':'H','weights':[[0,1]],'objective_weight':1,'F_index':0}),
 ):
  reject(name,lambda rec=rec:dual_margin(rows,bounds,rec))
 # Valid-looking but noncontradictory weight must not be accepted by leaf checker.
 reject('noncontradiction_at_physical_point',lambda:verify_child_new(point_parent,lab,{'mode':'FULL','proof':{'kind':'C','weights':[[0,1]]}}))
 zz=contract_homogeneous(point_parent,lab);assert zz['status']=='BOUNDED'
 reject('unknown_homogeneous_source',lambda:generalized_rows(zz['aux_image'],lab,['FAKE_TAIL_CONTACT']))
 reject('repeated_homogeneous_source',lambda:generalized_rows(zz['aux_image'],lab,['S02-','S02-']))
 reject('mixed_child_schema',lambda:verify_child_new(point_parent,lab,{'mode':'FULL','proof':{'kind':'I'},'sources':['S02-']}))
 # The full source may be feasible while a false alpha leaf is requested elsewhere;
 # no unsupported leaf type is allowed to supply a default safety statement.
 reject('unsupported_tail_or_default_safety_leaf',lambda:verify_child_new(parent,lab,{'mode':'FULL','proof':{'kind':'Q'}}))
 return {'rejection_controls':len(tests),'correctly_rejected':tests}
if __name__=='__main__':print(json.dumps(run(),indent=2))
