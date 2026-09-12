"""Parallel discovery in original-root envelopes; exact replay after every chunk.

Each worker owns one dyadic frontier, keeps every ancestor and pays no sibling.
Only grafted original-root checkpoints receive original-root scope.
V35 retains the repaired P rules and adds source-conditioned A safety leaves. An open root is not a proof.
"""
from pathlib import Path
from fractions import Fraction
from collections import deque
import argparse, concurrent.futures as cf, hashlib, json, os, shutil, subprocess, sys, time

# CQG nested original-root graft: each valid path is <=512, two may coexist.
sys.setrecursionlimit(max(sys.getrecursionlimit(),4096))
PINS={}  # populated from new immutable models by run_campaign.py

def digest(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()

def write_json(path,obj):
    path=Path(path);tmp=path.with_name(path.name+'.next')
    tmp.write_text(json.dumps(obj,indent=2)+'\n');os.replace(tmp,path)

_VERIFY_CACHE={}
def run_verify(exe,tree,allow_open=True):
    cache_key=(digest(exe),digest(tree),bool(allow_open))
    if cache_key in _VERIFY_CACHE:
        return dict(_VERIFY_CACHE[cache_key])
    p=subprocess.run([str(exe),str(tree)]+(['--allow-open'] if allow_open else []),capture_output=True,text=True)
    if p.returncode:raise RuntimeError('Exact rejection: '+p.stderr[-3000:])
    d=json.loads(p.stdout)
    if d['nodes']!=2*d['splits']+1 or d['leaves']+d['open']!=d['splits']+1:raise ValueError('Bad counters')
    _VERIFY_CACHE[cache_key]=dict(d)
    return d

def fields(line):
    if not line or not line.endswith(b'\n'):raise ValueError('Missing/truncated tree record')
    f=line.split();tag=f[0]
    if tag==b'S':
        if len(f)!=2:raise ValueError('Malformed split')
        return tag,int(f[1])
    if tag==b'O':
        if len(f)!=1:raise ValueError('Malformed open leaf')
    elif tag==b'A':
        if len(f)!=2 or not 0<=int(f[1])<=10:raise ValueError('Malformed alpha-safe leaf')
    elif tag in (b'R',b'P'):
        if len(f)!=2 or not 0<=int(f[1])<=3:raise ValueError('Malformed packet leaf')
    elif tag==b'C':
        if len(f)<2 or int(f[1])<1 or len(f)!=2+2*int(f[1]):raise ValueError('Malformed weighted leaf')
    else:raise ValueError('Unknown tree record')
    return tag,None

def root_box(data):return tuple(tuple(int(v)<<128 for v in row) for row in data['root_numerators'])

def children(lo,hi,j):
    if not 0<=j<len(lo) or (lo[j]+hi[j])%2:raise ValueError('Invalid exact split')
    m=(lo[j]+hi[j])//2
    if not lo[j]<m<hi[j]:raise ValueError('Empty exact split')
    a=list(hi);a[j]=m;b=list(lo);b[j]=m
    return (lo,tuple(a)),(tuple(b),hi)

def collect_frontiers(path,data,name):
    out=[]
    with Path(path).open('rb') as f:
        def visit(lo,hi,steps):
            tag,j=fields(f.readline())
            if tag==b'S':
                left,right=children(lo,hi,j)
                visit(*left,steps+[(j,0)]);visit(*right,steps+[(j,1)])
            elif tag==b'O':
                out.append({'model':name,'steps':steps,'lo':lo,'hi':hi})
        visit(*root_box(data),[])
        if f.read().strip():raise ValueError('Unvisited base records')
    return out

def key(steps):return ''.join(str(b) for _,b in steps)

def envelope(steps,payload=b'O\n'):
    for j,b in reversed(steps):
        payload=f'S {j}\n'.encode()+(payload+b'O\n' if b==0 else b'O\n'+payload)
    return payload

def copy_subtree(stream,out,on_open=None,path=''):
    line=stream.readline();tag,j=fields(line)
    if tag==b'O' and on_open is not None:on_open(path,out)
    else:
        out.write(line)
        if tag==b'S':
            copy_subtree(stream,out,on_open,path+'0');copy_subtree(stream,out,on_open,path+'1')

def copy_focused_payload(path,steps,out):
    """Reject missing, swapped or paid siblings; extract one exact envelope payload."""
    with Path(path).open('rb') as f:
        def descend(i):
            if i==len(steps):copy_subtree(f,out);return
            j,b=steps[i];tag,actual=fields(f.readline())
            if tag!=b'S' or actual!=j:raise ValueError('Envelope ancestor differs from frozen frontier')
            if b==1 and f.readline()!=b'O\n':raise ValueError('Non-owned left sibling is not O')
            descend(i+1)
            if b==0 and f.readline()!=b'O\n':raise ValueError('Non-owned right sibling is not O')
        descend(0)
        if f.read().strip():raise ValueError('Unvisited envelope tail')

def prepare_wave(work,wave,inputs,target):
    wave.mkdir();data={n:json.loads((work/'models'/n/'model.json').read_text()) for n in inputs}
    fronts=[];extra={n:{} for n in inputs}
    for n,path in inputs.items():
        fronts+=collect_frontiers(path,data[n],n)
    while len(fronts)<target:
        cand=[(len(e['steps']),i) for i,e in enumerate(fronts) if len(e['steps'])<450]
        if not cand:break
        _,i=min(cand);e=fronts.pop(i);rlo,rhi=root_box(data[e['model']])
        j=max(range(len(rlo)),key=lambda q:Fraction(e['hi'][q]-e['lo'][q],rhi[q]-rlo[q]))
        lr=children(e['lo'],e['hi'],j);extra[e['model']][key(e['steps'])]=j
        for b,(lo,hi) in enumerate(lr):fronts.append({'model':e['model'],'steps':e['steps']+[(j,b)],'lo':lo,'hi':hi})
    for n,path in inputs.items():
        dest=wave/(n+'_expanded.tree')
        def replace(path,out):
            if path not in extra[n]:out.write(b'O\n');return
            j=extra[n][path];out.write(f'S {j}\n'.encode());replace(path+'0',out);replace(path+'1',out)
        with Path(path).open('rb') as f,dest.open('wb') as out:
            copy_subtree(f,out,replace)
            if f.read().strip():raise ValueError('Unvisited source')
        info=run_verify(work/'models'/n/'verify',dest)
        write_json(wave/(n+'_EXPANDED_ACCEPTANCE.json'),info)
    jobs=[]
    # Broad frontiers first; every narrow frontier still has a queued owner.
    fronts.sort(key=lambda e:(len(e['steps']),e['model'],key(e['steps'])))
    for i,e in enumerate(fronts):
        job={**e,'id':f'frontier_{i:04d}','focus':key(e['steps'])};d=wave/'jobs'/job['id'];d.mkdir(parents=True)
        (d/'checkpoint.tree').write_bytes(envelope(e['steps']))
        job['directory']=str(d);job['model_sha256']=PINS[e['model']]
        job['initial_tree_sha256']=digest(d/'checkpoint.tree');job['rounds']=0
        write_json(d/'FRONTIER.json',job);jobs.append(job)
    manifest={'schema':'rho5.cqg.round45.original-root-frontiers.v1','jobs':jobs,
        'inputs':{n:{'path':str(p),'sha256':digest(p),'model_sha256':PINS[n]} for n,p in inputs.items()},
        'expanded':{n:{'path':str(wave/(n+'_expanded.tree')),'sha256':digest(wave/(n+'_expanded.tree'))} for n in inputs},
        'new_split_count':sum(len(z) for z in extra.values()),'root_and_rows_changed':False}
    write_json(wave/'FRONTIER_MANIFEST.json',manifest)
    return jobs,manifest

def job_chunk(job,work,seconds):
    d=Path(job['directory']);model=work/'models'/job['model'];stamp=str(time.time_ns());job['rounds']+=1
    if digest(model/'model.json')!=job['model_sha256']:raise ValueError('Worker model binding changed')
    with (d/(stamp+'_DISCOVERY.log')).open('w') as log:
        try:
            subprocess.run([str(model/'discover_focus'),str(d/'checkpoint.tree'),str(d/'next.tree'),str(seconds),'1000000',job['focus']],
                           stdout=log,stderr=subprocess.STDOUT,check=True, timeout=max(15.0, 2.0*seconds+5.0))
        except (subprocess.TimeoutExpired,subprocess.CalledProcessError):
            (d/'next.tree').unlink(missing_ok=True)
            raise
    info=run_verify(model/'verify',d/'next.tree');inside=info['open']-len(job['steps'])
    if inside<0:raise ValueError('Worker erased an unpaid ancestor sibling')
    # Validate focus ownership, not just the count of exterior unpaid siblings.
    with open(os.devnull,'wb') as sink:copy_focused_payload(d/'next.tree',job['steps'],sink)
    info.update(target_open=inside,model_sha256=job['model_sha256'],tree_sha256=digest(d/'next.tree'),
                search_seconds=seconds,focus=job['focus'],rounds=job['rounds'],scope='ONE_FRONTIER_ONLY_NO_WHOLE_ROOT_CREDIT')
    write_json(d/(stamp+'_ACCEPTANCE.json'),info)
    os.replace(d/'next.tree',d/'checkpoint.tree');write_json(d/'STATUS.json',info)
    return info

def execute_wave(work,wave,jobs,workers,deadline,chunk):
    queue=deque(jobs);active={};completed=[];failures=[];chunks=0;started=time.monotonic();last=0
    with cf.ThreadPoolExecutor(max_workers=workers) as pool:
        while queue or active:
            while queue and len(active)<workers and time.monotonic()<deadline:
                job=queue.popleft();budget=min(chunk,max(.01,deadline-time.monotonic()))
                active[pool.submit(job_chunk,job,work,budget)]=job
            if not active:break
            done,_=cf.wait(active,timeout=2,return_when=cf.FIRST_COMPLETED)
            for future in done:
                job=active.pop(future)
                try:info=future.result();chunks+=1
                except Exception as e:
                    failures.append({'job':job['id'],'error':str(e)});continue
                if info['target_open']==0:completed.append(job['id'])
                else:queue.append(job)
            now=time.monotonic()
            if now-last>30:
                status={'status':'DISCOVERY_WAVE_RUNNING','completed_frontiers':len(completed),
                    'active_workers':len(active),'queued_frontiers':len(queue),'failed_frontiers':len(failures),
                    'accepted_chunks':chunks,'elapsed_seconds':now-started,'whole_root_height_credit':False}
                write_json(wave/'PROGRESS.json',status);print(json.dumps(status),flush=True);last=now
            # Repartition a small surviving workload at the next exact barrier.
            if 0<len(queue)+len(active)<max(2,workers//2) and now-started>chunk:
                deadline=min(deadline,now)
        # All in-flight chunks have ended before the original-root graft below.
    result={'completed_frontiers':completed,'failures':failures,'accepted_chunks':chunks,
            'elapsed_seconds':time.monotonic()-started,'checkpoint_frontiers_preserved':len(jobs)}
    write_json(wave/'WAVE_DISCOVERY_RESULT.json',result);return result

def graft_wave(work,wave,jobs,manifest):
    results={}
    for name,base in manifest['expanded'].items():
        if digest(base['path'])!=base['sha256']:raise ValueError('Expanded base changed')
        selected={j['focus']:j for j in jobs if j['model']==name};used=set();output=wave/(name+'_grafted.tree')
        def replace(path,out):
            if path not in selected or path in used:raise ValueError('Missing/duplicate frontier ownership')
            job=selected[path];used.add(path);checkpoint=Path(job['directory'])/'checkpoint.tree'
            status=Path(job['directory'])/'STATUS.json'
            expected=json.loads(status.read_text())['tree_sha256'] if status.exists() else job['initial_tree_sha256']
            if digest(checkpoint)!=expected:raise ValueError('Worker checkpoint differs from last accepted snapshot')
            copy_focused_payload(checkpoint,job['steps'],out)
        with Path(base['path']).open('rb') as f,output.open('wb') as out:
            copy_subtree(f,out,replace)
            if f.read().strip():raise ValueError('Unvisited expanded records')
        if used!=set(selected):raise ValueError('Unused frontier')
        info=run_verify(work/'models'/name/'verify',output)
        info.update(model_sha256=PINS[name],tree_sha256=digest(output),tree=str(output),
                    original_root_accepted=True,frontiers_grafted=len(used),root_and_model_unchanged=True)
        if info['open']==0:
            strict=run_verify(work/'models'/name/'verify',output,False)
            info['strict_original_acceptance']=strict
            p=subprocess.run([sys.executable,str(work/'verify_task.py'),str(work/'models'/name),'--tree',str(output)],capture_output=True,text=True)
            (wave/(name+'_COLD_REPLAY.log')).write_text(p.stdout+p.stderr)
            if p.returncode:raise RuntimeError('Fresh semantic original-root acceptance failed')
            info['semantic_cold_replay']=json.loads(p.stdout)
        write_json(wave/(name+'_ORIGINAL_ROOT_ACCEPTANCE.json'),info);results[name]=info
    return results
