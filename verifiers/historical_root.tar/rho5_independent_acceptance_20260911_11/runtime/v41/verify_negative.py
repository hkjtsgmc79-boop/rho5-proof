"""Deliberate malformed-proof rejection; not arbitrary perturbation claims."""
from pathlib import Path
from copy import deepcopy
import json
from source_access import ROOT,SOURCE,fs
from dual_box import replay_trace,common_contract,rows_and_bounds,bound_value
from v41_protocol import verify,bind,RULE_FILES

def run():
    index=json.loads((ROOT/'INSERTION_INDEX.json').read_text())
    box=index[0]['box'];node=json.loads((ROOT/index[0]['certificate']).read_text())
    accepted=verify(box,node);assert accepted['status']=='EMPTY'
    tests=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,KeyError,IndexError,AssertionError,ZeroDivisionError):tests.append(name);return
        raise AssertionError('Accepted bad control: '+name)
    for field in ('rule','rule_identity','model_sha256','round50_reported_root_sha256','box_sha256'):
        x=deepcopy(node);x[field]='wrong';reject('wrong_'+field,lambda x=x:verify(box,x))
    x=deepcopy(node);x['trace']['terminal']={'kind':'O'};reject('OPEN_in_full_mode',lambda:verify(box,x))
    x=deepcopy(node);x['trace']['terminal']={'kind':'I'};x['trace']['waves']=[];reject('false_interval_terminal',lambda:verify(box,x))
    x=deepcopy(node);x['trace']['profile']='UNTRUSTED';reject('unknown_profile',lambda:verify(box,x))
    x=deepcopy(node);x['trace']['label']='B1|E:H';reject('conditional_trace_smuggled_into_U41',lambda:verify(box,x))
    x=deepcopy(node);x['extra']=True;reject('unknown_wrapper_field',lambda:verify(box,x))
    x=deepcopy(node);del x['trace']['terminal'];reject('missing_terminal',lambda:verify(box,x))
    x=deepcopy(node);x['trace']['terminal']={'kind':'Q'};reject('fake_safe_Q',lambda:verify(box,x))
    x={'kind':'G41',**bind(box),'children':{}};reject('missing_189_children',lambda:verify(box,x))
    x={'kind':'G41',**bind(box),'children':{lab:{'engine':'OPEN'}for lab in fs.GRAPH_LABELS}};reject('all_OPEN_graph_in_full_mode',lambda:verify(box,x))
    assert verify(box,x,allow_open=True)['status']=='OPEN'
    x=deepcopy(node);x['kind']='C';reject('bound_sequence_masquerading_as_old_C',lambda:verify(box,x))
    # Test individual bound schemas on a real frozen relaxation.
    out=common_contract(fs.parent_enclosure(box));rows,boxes=rows_and_bounds(out['aux_image'])
    record=node['trace']['waves'][0][0]
    for field,value in [('coordinate',24),('coordinate',True),('coordinate',0.0),('direction',0),('direction',True),('objective_weight',0),('objective_weight',-1),('objective_weight',1.0)]:
        r=deepcopy(record);r[field]=value;reject(f'bad_bound_{field}_{value!r}',lambda r=r:bound_value(rows,boxes,r))
    for label,weights in [('empty',[]),('zero',[[0,0]]),('negative',[[0,-1]]),('duplicate',[[0,1],[0,1]]),('range',[[len(rows),1]]),('float',[[0,1.0]]),('bool',[[True,1]])]:
        r=deepcopy(record);r['weights']=weights;reject('weights_'+label,lambda r=r:bound_value(rows,boxes,r))
    x=deepcopy(node);x['trace']['terminal']={'kind':'C','weights':[[0,0]]};reject('zero_final_weight',lambda:verify(box,x))
    # These are real-valued boxes, but parser values must be exact strings/ints.
    x=deepcopy(box);x[0][0]=True;reject('boolean_box',lambda:verify(x,node))
    x=deepcopy(box);x[0][0]=1.0;reject('float_box',lambda:verify(x,node))
    return dict(rejection_controls=len(tests),controls=tests,partial_graph_stays_OPEN=True)
if __name__=='__main__':print(json.dumps(run(),indent=2))
