"""Optional, untrusted LP discovery. Every retained bound is accepted by Fraction.
Run only in a separate directory. A time limit is a soft search budget, not a
promise of completion; a current LP and final exact replay can finish afterward.
"""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[key]='1'
from pathlib import Path
import time,json,tempfile
from source_access import fs
from dual_box import common_contract,rows_and_bounds,bound_value,apply_wave,replay_trace
from v41_protocol import wrap,verify

def atomic_json(path,data):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    fd,tmp=tempfile.mkstemp(dir=path.parent,prefix=path.name+'.',suffix='.tmp')
    try:
        with os.fdopen(fd,'w',encoding='utf-8')as f:
            json.dump(data,f,sort_keys=True,separators=(',',':'));f.write('\n');f.flush();os.fsync(f.fileno())
        os.replace(tmp,path)
    finally:
        if os.path.exists(tmp):os.unlink(tmp)

def bound_proposals(rows,boxes,deadline,limit=16):
    import numpy as np
    from scipy.optimize import linprog
    n=len(boxes);center=np.array([float((b.lo+b.hi)/2)for b in boxes]);half=np.array([float((b.hi-b.lo)/2)for b in boxes])
    mat=np.zeros((len(rows),n));rhs=np.zeros(len(rows))
    for i,(aa,bb)in enumerate(rows):
        rhs[i]=float(bb)
        for j,c in aa.items():mat[i,j]=float(c)
    bb=rhs-mat@center;aa=mat*half
    norm=np.maximum(1e-9,np.maximum(abs(bb),np.max(abs(aa),axis=1)))
    aa/=norm[:,None];bb/=norm;options=[]
    for i in range(24):
      if half[i]<1e-12:continue
      for sign in(1,-1):
        if time.monotonic()>=deadline:break
        obj=np.zeros(n);obj[i]=-sign*half[i]
        res=linprog(obj,A_ub=aa,b_ub=bb,bounds=[(-1,1)]*n,method='highs',options={'time_limit':1})
        if not res.success:continue
        old=float(boxes[i].hi if sign==1 else -boxes[i].lo)
        if old-(-res.fun+sign*center[i])<max(1e-9,half[i]*1e-4):continue
        raw=-res.ineqlin.marginals/norm
        if not np.all(np.isfinite(raw)):continue
        scale=10**10;weights=[max(0,int(round(float(x)*scale)))for x in raw]
        rec=dict(coordinate=i,direction=sign,objective_weight=scale,weights=[[j,w]for j,w in enumerate(weights)if w])
        if not rec['weights']:continue
        exact=bound_value(rows,boxes,rec)
        gain=(boxes[i].hi if sign==1 else -boxes[i].lo)-exact
        if gain>0:options.append((float(gain)/max(half[i],1e-20),rec))
    options.sort(key=lambda v:-v[0])
    return [rec for _,rec in options[:limit]]

def discover_parent(box,output,profile='BASE',max_waves=3,seconds=120):
    if max_waves<0 or max_waves>128 or seconds<0:raise ValueError('Invalid budget')
    output=Path(output);start=time.monotonic();deadline=start+seconds
    if output.exists():
        node=json.loads(output.read_text());accepted=verify(box,node,allow_open=True)
        if node['kind']!='U41' or node['trace']['profile']!=profile:raise ValueError('Cannot reuse another profile/root')
        if accepted['status']!='OPEN':return accepted
        trace=node['trace']
    else:
        trace=dict(profile=profile,waves=[],terminal={'kind':'O'})
    out=common_contract(fs.parent_enclosure(box),profile=profile)
    for wave in trace['waves']:out=apply_wave(out,wave,profile=profile)
    atomic_json(output,wrap(box,trace)) # a valid open prefix survives interruption
    reason='wave_budget'
    while True:
        terminal=None
        if out['status']=='EMPTY':terminal={'kind':'I'}
        elif fs.safe_port(out['aux_image'])is not None:terminal={'kind':'A'}
        elif time.monotonic()<deadline:
            # Import only on the optional discovery path. Proposal verifies exact
            # margins, but the final parent replay below checks them again.
            from proposal import propose_rows
            rows,boxes=rows_and_bounds(out['aux_image'],profile=profile)
            terminal=propose_rows(rows,boxes)
        if terminal:
            trace['terminal']=terminal
            result=verify(box,wrap(box,trace),cross_check=True)
            atomic_json(output,wrap(box,trace));reason='certified_terminal';break
        if len(trace['waves'])>=max_waves:break
        if time.monotonic()>=deadline:reason='soft_budget';break
        rows,boxes=rows_and_bounds(out['aux_image'],profile=profile)
        wave=bound_proposals(rows,boxes,deadline)
        if not wave:reason='no_retained_proposal';break
        out=apply_wave(out,wave,profile=profile,cross_check=True)
        trace['waves'].append(wave)
        atomic_json(output,wrap(box,trace))
    result=verify(box,wrap(box,trace),allow_open=True,cross_check=True)
    receipt=dict(**result,discovery_reason=reason,seconds=time.monotonic()-start,
                 full_tree_modified=False,continuous_splits_added=0,profile=profile)
    atomic_json(str(output)+'.receipt.json',receipt)
    return receipt
if __name__=='__main__':
    import argparse
    a=argparse.ArgumentParser();a.add_argument('box');a.add_argument('--output',required=True)
    a.add_argument('--profile',choices=('BASE','PIVOT','CYCLE','PIVOT_CYCLE'),default='BASE')
    a.add_argument('--max-waves',type=int,default=3);a.add_argument('--seconds',type=float,default=120)
    ns=a.parse_args();box=json.loads(Path(ns.box).read_text());box=box['box']if isinstance(box,dict)else box
    print(json.dumps(discover_parent(box,ns.output,ns.profile,ns.max_waves,ns.seconds),indent=2))
