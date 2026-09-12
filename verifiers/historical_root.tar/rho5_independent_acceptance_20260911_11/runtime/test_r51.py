from concurrent.futures import ProcessPoolExecutor
import copy,json,multiprocessing
from r51_protocol import *
def check(args):return verify_leaf(*args)
def main():
 items=json.loads((ROOT/'v41/INSERTION_INDEX.json').read_text());a=items[0];b=items[9]
 n=json.loads((ROOT/'v41'/a['certificate']).read_text());n9=json.loads((ROOT/'v41'/b['certificate']).read_text())
 assert check((a['box'],n,'native'))=='EMPTY'
 with ProcessPoolExecutor(max_workers=2,mp_context=multiprocessing.get_context('spawn'))as p:
  assert list(p.map(check,[(a['box'],n,'fraction'),(b['box'],n9,'fraction')]))==['EMPTY','EMPTY']
 tested=[]
 def reject(name,fn):
  try:fn()
  except (ValueError,AssertionError,KeyError,TypeError):tested.append(name);return
  raise AssertionError('bad integration input accepted: '+name)
 wrong=copy.deepcopy(n);wrong['box_sha256']='0'*64;reject('wrong_actual_box',lambda:verify_leaf(a['box'],wrong))
 wrong=copy.deepcopy(n);wrong['rule_identity']='0'*64;reject('wrong_rule',lambda:verify_leaf(a['box'],wrong))
 partial=json.loads((ROOT/'v41'/items[49]['certificate']).read_text());reject('OPEN_U41',lambda:verify_leaf(items[49]['box'],partial))
 conditional=json.loads((ROOT/'v41/controls/conditional49_partial.json').read_text());reject('partial_G41',lambda:verify_leaf(items[49]['box'],conditional))
 wrong=copy.deepcopy(n);wrong['kind']='C';reject('not_legacy_C',lambda:verify_leaf(a['box'],wrong))
 root={'model_sha256':sha(tp.MODEL),'root_path':'','nodes':[{'kind':'O'}]};structure(root)
 for key,value in [('root_path','0'),('model_sha256','0'*64),('nodes',[{'kind':'S','axis':0}])]:
  wrong=copy.deepcopy(root);wrong[key]=value;reject('root_'+key,lambda:structure(wrong))
 assert old.v40.rule_identity()=='4b1d191181faaea707591fea266427111004ba27e599604c4230fbf58f74bd7e'
 assert v41.IDENTITY['b17_model_sha256']==sha(tp.MODEL)
 for name in ('full_source.py','protocol.py','bootstrap.py'):
  assert sha(ROOT/'v40'/name)==sha(v41.SOURCE/'v40'/name)
 print(json.dumps({'status':'ROUND51_INTEGRATION_CONTROLS_PASS','BASE_and_PIVOT_CYCLE_checked':True,'sparse_dense_parallel_consistent':True,'negative_controls':tested,'legacy_V40_identity_unchanged':True}))
if __name__=='__main__':main()
