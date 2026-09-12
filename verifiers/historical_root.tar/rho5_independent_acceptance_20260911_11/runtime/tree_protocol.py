"""Reference exact coverage protocol. OPEN is never an alpha proof.
Root identity binds the original 17-frame root, not a canonical-image root.
"""
import json,hashlib
from pathlib import Path
from fractions import Fraction as Q
from interval_capacity import I,root_box
from relaxation import verify_leaf
ROOT=Path(__file__).parent
MODEL=ROOT/'models/B17_FULL.json'

def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def halve(box,axis):
    if type(axis)is not int or not 0<=axis<17:raise ValueError('invalid split coordinate')
    v=box[axis];m=(v.lo+v.hi)/2
    if m==v.lo or m==v.hi:raise ValueError('zero-width split')
    L=box.copy();R=box.copy();L[axis]=I(v.lo,m);R[axis]=I(m,v.hi)
    return L,R

def task_box(task=None):
    if task is None:return root_box(),''
    tasks=json.loads((ROOT/'models/PARTITION40.json').read_text())
    if type(task)is not int or not 0<=task<len(tasks['leaves']):raise ValueError('task index outside partition')
    leaf=tasks['leaves'][task];box=root_box()
    for st in leaf['route']:
        if st['child']not in(0,1):raise ValueError('bad child')
        box=halve(box,st['axis'])[st['child']]
    if [v.data()for v in box]!=leaf['box']:raise ValueError('partition box mismatch')
    return box,leaf['path']

def empty_tree(task=None):
    box,path=task_box(task)
    return {'model_sha256':digest(MODEL),'task':task,'root_path':path,'nodes':[{'kind':'O'}]}

def verify_tree(data,*,allow_open=False):
    if data.get('model_sha256')!=digest(MODEL):raise ValueError('wrong frozen model')
    box,path=task_box(data.get('task'))
    if data.get('root_path')!=path:raise ValueError('wrong root ownership')
    nodes=data.get('nodes')
    if not isinstance(nodes,list)or not nodes:raise ValueError('empty tree')
    stack=[(box,0)];counts={'nodes':0,'splits':0,'contradictions':0,'alpha_safe':0,'open':0,'max_depth':0}
    i=0
    while stack:
        b,depth=stack.pop()
        if i>=len(nodes):raise ValueError('truncated tree')
        node=nodes[i];i+=1;counts['nodes']+=1;counts['max_depth']=max(counts['max_depth'],depth)
        if not isinstance(node,dict):raise ValueError('bad node')
        kind=node.get('kind')
        if kind=='S':
            if set(node)!={'kind','axis'}:raise ValueError('bad split schema')
            L,R=halve(b,node['axis']);stack.extend([(R,depth+1),(L,depth+1)]);counts['splits']+=1
        elif kind=='O':counts['open']+=1
        elif kind in('E','C','H'):
            status=verify_leaf(b,node)
            counts['contradictions' if status=='EMPTY'else 'alpha_safe']+=1
        else:raise ValueError('unknown node type')
    if i!=len(nodes):raise ValueError('unvisited records')
    if counts['nodes']!=2*counts['splits']+1:raise ValueError('binary coverage identity')
    if counts['open']and not allow_open:raise ValueError(f"{counts['open']} unpaid frontiers")
    counts['status']='COMPLETE_ALPHA_COVERAGE'if not counts['open']else'PARTIAL_EXACT_COVERAGE_ONLY'
    counts['whole_B_closed']=not counts['open']and data.get('task')is None
    return counts

def verify_partition():
    f=ROOT/'models/PARTITION40.json';p=json.loads(f.read_text())
    if p['model_sha256']!=digest(MODEL):raise ValueError('partition model mismatch')
    leaves=p['leaves'];paths={x['path']:x for x in leaves}
    if len(paths)!=40:raise ValueError('need 40 distinct leaves')
    splits=p['splits'];seen=[]
    def walk(path,box,route):
        if path in paths:
            leaf=paths[path]
            if leaf['route']!=route or leaf['box']!=[v.data()for v in box]:raise ValueError('bad leaf ownership')
            seen.append(path);return
        if path not in splits:raise ValueError('missing partition child')
        axis=splits[path];L,R=halve(box,axis)
        walk(path+'0',L,route+[{'axis':axis,'child':0}]);walk(path+'1',R,route+[{'axis':axis,'child':1}])
    walk('',root_box(),[])
    if set(seen)!=set(paths)or len(splits)!=39:raise ValueError('extraneous partition record')
    return {'partition_leaves':40,'splits':39,'coverage':'EXACT_FULL_ORIGINAL_FRAME_ROOT','proof_status':'ALL_TASKS_INITIALIZED_OPEN'}

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('file');p.add_argument('--allow-open',action='store_true');a=p.parse_args()
    try:r=verify_tree(json.loads(Path(a.file).read_text()),allow_open=a.allow_open)
    except (ValueError,KeyError,TypeError,AssertionError)as e:print(json.dumps({'status':'REJECTED','error':str(e)}));raise SystemExit(2)
    print(json.dumps(r,ensure_ascii=False,indent=2))
