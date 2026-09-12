#!/usr/bin/env python3
"""Same B17 root/leaf protocol, fair frontier discovery, one exact task replay."""
from pathlib import Path
from collections import Counter, deque
import argparse, fcntl, hashlib, json, os, time
from fractions import Fraction as Q
import tree_protocol as tp
import native_backend as native
from interval_capacity import root_box

ROOT=Path(__file__).resolve().parent

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def identity():
    names=('MANIFEST.json','b17_native.cpp','b17_native_data.hpp','native_backend.py','tree_protocol.py','interval_capacity.py','libb17_native.so','HIGH_VALUE_RULE.json','high_value_contraction.py','high_value_reference.py')
    return hashlib.sha256(json.dumps({n:sha(ROOT/n)for n in names},sort_keys=True).encode()).hexdigest()

def structure(data,task):
    if data.get('model_sha256')!=sha(tp.MODEL):raise ValueError('wrong frozen model')
    if type(data.get('task'))is not type(task)or data.get('task')!=task:raise ValueError('wrong task owner')
    box,path=tp.task_box(task)
    if data.get('root_path')!=path:raise ValueError('wrong root path')
    records=data.get('nodes')
    if not isinstance(records,list)or not records:raise ValueError('empty tree')
    slots=1
    for record in records:
        if slots<=0 or not isinstance(record,dict):raise ValueError('invalid subtree envelope')
        kind=record.get('kind')
        if kind=='S':
            axis=record.get('axis')
            if set(record)!={'kind','axis'}or type(axis)is not int or not 0<=axis<17:raise ValueError('bad split')
            slots+=1
        elif kind=='O':slots-=1
        elif kind in ('E','C','H'):native.validate_record(record);slots-=1
        else:raise ValueError('invalid leaf type')
    if slots!=0:raise ValueError('truncated subtree')
    return box,path

def run(task,seconds,max_nodes,output,max_depth=96,chunk_nodes=64):
    if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
    path=Path(output);path.parent.mkdir(parents=True,exist_ok=True)
    with path.with_suffix('.writer.lock').open('a')as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        start=time.monotonic();data=json.loads(path.read_text())if path.exists()else tp.empty_tree(task)
        box,route=structure(data,task);engine_id=identity();receipt_path=path.with_suffix(path.suffix+'.receipt.json')
        if path.exists()and receipt_path.exists():
            old_receipt=json.loads(receipt_path.read_text())
            if old_receipt.get('open')==0 and old_receipt.get('tree_sha256')==sha(path)and old_receipt.get('native_identity')==engine_id:
                return {**old_receipt,'new_attempts':0,'discovery_seconds':0,'verification_seconds':0,'seconds':time.monotonic()-start,'already_closed':True}
        root=[None,None,None];stack=[(root,box,0)];frontiers=deque();iterator=iter(data['nodes'])
        while stack:
            item,b,depth=stack.pop();record=next(iterator);item[0]=record
            if record['kind']=='S':
                left,right=tp.halve(b,record['axis']);item[1]=[None,None,None];item[2]=[None,None,None]
                stack.extend([(item[2],right,depth+1),(item[1],left,depth+1)])
            elif record['kind']=='O':frontiers.append((item,b,depth,1))
        attempts=0;stops=Counter();widths=[v.hi-v.lo for v in root_box()];search_start=time.monotonic()
        def fresh(item,b,depth,allowance):
            nonlocal attempts
            if depth>=max_depth:stops['depth']+=1;return
            if attempts>=max_nodes:stops['node_budget']+=1;return
            if time.monotonic()-search_start>=seconds:stops['time_budget']+=1;return
            if allowance[0]<=0:frontiers.append((item,b,depth,chunk_nodes));return
            attempts+=1;allowance[0]-=1;record=native.propose(b)
            if record:item[0]=record;return
            axis=max(range(17),key=lambda i:(b[i].hi-b[i].lo)/widths[i])
            item[0]={'kind':'S','axis':axis};item[1]=[{'kind':'O'},None,None];item[2]=[{'kind':'O'},None,None]
            left,right=tp.halve(b,axis);fresh(item[1],left,depth+1,allowance);fresh(item[2],right,depth+1,allowance)
        while frontiers and attempts<max_nodes and time.monotonic()-search_start<seconds:
            item,b,depth,allowance=frontiers.popleft();fresh(item,b,depth,[allowance])
        search_seconds=time.monotonic()-search_start
        if attempts>=max_nodes:stops['node_budget']+=1
        if search_seconds>=seconds:stops['time_budget']+=1
        records=[];stack=[root];kind_counts=Counter();open_volume=Q(0);depth_stack=[0]
        while stack:
            item=stack.pop();depth=depth_stack.pop();records.append(item[0]);kind_counts[item[0]['kind']]+=1
            if item[0]['kind']=='S':stack.extend([item[2],item[1]]);depth_stack.extend([depth+1,depth+1])
            elif item[0]['kind']=='O':open_volume+=Q(1,2**depth)
        data['nodes']=records;native.install();before=time.monotonic();result=tp.verify_tree(data,allow_open=True)
        verify_seconds=time.monotonic()-before
        temporary=path.with_suffix(path.suffix+'.pending');temporary.write_text(json.dumps(data,separators=(',',':'),sort_keys=True)+'\n')
        tree_hash=sha(temporary);os.replace(temporary,path)
        result.update({'task':task,'root_path':route,'tree_sha256':tree_hash,'model_sha256':data['model_sha256'],
                       'native_identity':engine_id,'new_attempts':attempts,'discovery_seconds':search_seconds,
                       'verification_seconds':verify_seconds,'seconds':time.monotonic()-start,
                       'stops':dict(stops),'kinds':dict(kind_counts),'requested_nodes':max_nodes,'requested_seconds':seconds,
                       'max_depth_limit':max_depth,'normalized_open_box_volume':str(open_volume),
                       'volume_is_geometric_diagnostic_not_proof_completion_fraction':True,
                       'strategy':'one first visit per inherited OPEN, then fair bounded DFS chunks',
                       'all_original_siblings_preserved':True})
        temporary=receipt_path.with_suffix('.pending');temporary.write_text(json.dumps(result,indent=2)+'\n');os.replace(temporary,receipt_path)
        return result

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--task',type=int,required=True);parser.add_argument('--seconds',type=float,default=120);parser.add_argument('--nodes',type=int,default=4096);parser.add_argument('--output',type=Path,required=True);parser.add_argument('--max-depth',type=int,default=96);args=parser.parse_args()
    print(json.dumps(run(args.task,args.seconds,args.nodes,args.output,args.max_depth),indent=2))
