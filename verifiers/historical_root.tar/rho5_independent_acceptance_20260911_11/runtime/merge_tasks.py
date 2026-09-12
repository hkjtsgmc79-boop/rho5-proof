#!/usr/bin/env python3
"""Graft all 40 EXACT task checkpoints back to the immutable original B17 root.
Missing tasks are errors. Without --allow-open, any remaining frontier rejects.
"""
import argparse,json
from pathlib import Path
from tree_protocol import verify_partition,empty_tree,verify_tree,ROOT

def merge(directory,*,allow_open=False):
    verify_partition();part=json.loads((ROOT/'models/PARTITION40.json').read_text());tasks={}
    for leaf in part['leaves']:
        path=Path(directory)/f"task_{leaf['task']:02d}.json"
        item=json.loads(path.read_text())
        if item.get('task')!=leaf['task']:raise ValueError('task filename/ownership mismatch')
        verify_tree(item,allow_open=allow_open);tasks[leaf['path']]=item['nodes']
    nodes=[]
    def visit(path):
        if path in tasks:nodes.extend(tasks[path]);return
        nodes.append({'kind':'S','axis':part['splits'][path]});visit(path+'0');visit(path+'1')
    visit('');data=empty_tree();data['nodes']=nodes
    result=verify_tree(data,allow_open=allow_open)
    return data,result
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('directory');p.add_argument('--output',default='merged.json');p.add_argument('--allow-open',action='store_true');a=p.parse_args()
    try:d,r=merge(a.directory,allow_open=a.allow_open)
    except (ValueError,OSError,KeyError)as e:print(json.dumps({'status':'REJECTED','error':str(e)}));raise SystemExit(2)
    Path(a.output).write_text(json.dumps(d,sort_keys=True,separators=(',',':'))+'\n');print(json.dumps(r,indent=2))
