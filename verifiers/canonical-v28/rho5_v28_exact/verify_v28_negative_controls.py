import json,gzip,tempfile,copy,contextlib,io
from pathlib import Path
import verify_v28_coverage as v
v.LIB=v.build();cp=json.loads((v.BASE/'RHO5_V26_REBUILT/global_localization_partial_checkpoint.json').read_text())
front=next(x for x in cp['open_frontier'] if int(x['node'])==8663927)
with gzip.open(v.BASE/'certs/front_8663927.jsonl.gz','rt') as f:orig=[json.loads(ln) for ln in f]
assert len(orig)==2 and orig[1]['kind']=='F'
def bad_weight(a):a[1]['weights'][0][1]=-1
def bad_combo(a):a[1]['weights']=[[0,1]]
def bad_f(a):a[0]['f']='4132518/1000000'
def bad_root(a):a[0]['root_lo'][0]+=1
def bad_inside(a):a[1]={'node':1,'kind':'Q'}
def bad_open(a):a[1]={'node':1,'kind':'OPEN'}
def bad_cut(a):a[1]={'node':1,'kind':'B','axis':0,'cut':a[0]['root_lo'][0]-1}
def truncated(a):a.pop()
def bad_index(a):a[1]['weights']=[[999,1]]
tests=[bad_weight,bad_combo,bad_f,bad_root,bad_inside,bad_open,bad_cut,truncated,bad_index]
with tempfile.TemporaryDirectory() as td:
    p=Path(td)/'front_8663927.jsonl.gz'
    for mutate in tests:
        data=copy.deepcopy(orig);mutate(data)
        with gzip.open(p,'wt') as f:
            for r in data:f.write(json.dumps(r)+'\n')
        try:
            with contextlib.redirect_stdout(io.StringIO()):v.graft(front,Path(td))
        except (ValueError,EOFError,KeyError,IndexError):pass
        else:raise AssertionError('corruption was accepted: '+mutate.__name__)
print('V28_NEGATIVE_CONTROLS_PASS',len(tests),'invalid artifacts rejected')
