from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
import copy,json,multiprocessing
from r50_protocol import *
def check(x):return verify_leaf(x[0],x[1],x[2])
def main():
 cert=json.loads((ROOT/'v40/evidence/parents/sample_00.json').read_text());box=cert['box'];node={'kind':'W40','certificate':cert}
 assert check((box,node,'fraction'))=='EMPTY'
 with ProcessPoolExecutor(max_workers=2,mp_context=multiprocessing.get_context('spawn'))as p:
  assert list(p.map(check,[(box,node,b)for b in ('native','fraction')]))==['EMPTY','EMPTY']
 tested=[]
 def reject(name,fn):
  try:fn()
  except (ValueError,AssertionError,KeyError,TypeError):tested.append(name);return
  raise AssertionError('invalid accepted: '+name)
 wrong=copy.deepcopy(node);wrong['certificate']['box'][0][0]='0'
 reject('actual_box_binding',lambda:verify_leaf(box,wrong))
 wrong=copy.deepcopy(node);wrong['certificate']['rule_identity']='0'*64
 reject('wrong_W40_rule',lambda:verify_leaf(box,wrong))
 partial=json.loads((ROOT/'v40/evidence/parents/sample_05.json').read_text())
 reject('partial_W40_cannot_pay_parent',lambda:verify_leaf(partial['box'],{'kind':'W40','certificate':partial}))
 reject('W40_cannot_be_legacy_C',lambda:verify_leaf(box,{'kind':'C','certificate':cert}))
 root={'model_sha256':sha(tp.MODEL),'root_path':'','nodes':[{'kind':'O'}]};structure(root)
 for key,val in [('model_sha256','0'*64),('root_path','0'),('nodes',[{'kind':'S','axis':0}]),('nodes',[{'kind':'S','axis':True},{'kind':'O'},{'kind':'O'}])]:
  x=copy.deepcopy(root);x[key]=val;reject('root_'+key+'_'+str(len(tested)),lambda:structure(x))
 # Nested old reference files must coincide with the already loaded frozen old implementation.
 for name in ('graph_protocol.py','graph_contract.py','prefix_graph.py'):
  assert sha(ROOT/'v39'/name)==sha(v40.bootstrap.V39/name)
 assert v40.MODEL_SHA==sha(tp.MODEL)
 print(json.dumps({'status':'R50_W40_INTEGRATION_CONTROLS_PASS','serial_and_parallel_agree':True,'negative_controls':tested,'new_reference_is_same_implementation':True}))
if __name__=='__main__':main()
