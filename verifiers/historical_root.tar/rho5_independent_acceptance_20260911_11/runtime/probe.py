#!/usr/bin/env python3
"""Bounded reference search, not a performance-certified production scheduler.
Discovery needs SciPy; every proposal and final checkpoint is exactly checked.
--seconds is a soft discovery limit (one LP/acceptance may finish afterwards).
Reusing --output resumes its exact same root/task. Ctrl-C preserves prior file.
"""
import argparse,json,time,os
from pathlib import Path
from tree_protocol import empty_tree,task_box,halve,verify_tree
from interval_capacity import root_box
from relaxation import propose

def run(task=None, seconds=30, max_nodes=64, output='checkpoint.json', max_depth=96):
    path=Path(output)
    data=json.loads(path.read_text())if path.exists()else empty_tree(task)
    if data.get('task')!=task:raise ValueError('existing checkpoint belongs to another task')
    verify_tree(data,allow_open=True)
    old=data['nodes'];cursor=0;out=[];attempts=0;start=time.monotonic()
    widths=[v.hi-v.lo for v in root_box()]
    def fresh(b,depth):
        nonlocal attempts
        if attempts>=max_nodes or time.monotonic()-start>=seconds or depth>=max_depth:
            out.append({'kind':'O'});return
        attempts+=1;record=propose(b)
        if record:out.append(record);return
        axis=max(range(17),key=lambda i:(b[i].hi-b[i].lo)/widths[i])
        out.append({'kind':'S','axis':axis});L,R=halve(b,axis)
        fresh(L,depth+1);fresh(R,depth+1)
    def visit(b,depth):
        nonlocal cursor
        node=old[cursor];cursor+=1
        if node['kind']=='S':
            out.append(node);L,R=halve(b,node['axis']);visit(L,depth+1);visit(R,depth+1)
        elif node['kind']=='O':fresh(b,depth)
        else:out.append(node)
    visit(task_box(task)[0],0)
    assert cursor==len(old)
    data['nodes']=out;result=verify_tree(data,allow_open=True)
    result.update({'new_attempts':attempts,'seconds':time.monotonic()-start,'task':task})
    path.parent.mkdir(parents=True,exist_ok=True)
    temp=path.with_suffix(path.suffix+'.pending')
    temp.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n');os.replace(temp,path)
    path.with_suffix(path.suffix+'.receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    return result
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--task',type=int);p.add_argument('--seconds',type=float,default=30);p.add_argument('--nodes',type=int,default=64);p.add_argument('--output',default='checkpoint.json');a=p.parse_args()
    try:r=run(a.task,a.seconds,a.nodes,a.output)
    except KeyboardInterrupt:print('INTERRUPTED: previous accepted checkpoint unchanged');raise SystemExit(130)
    print(json.dumps(r,ensure_ascii=False,indent=2))
