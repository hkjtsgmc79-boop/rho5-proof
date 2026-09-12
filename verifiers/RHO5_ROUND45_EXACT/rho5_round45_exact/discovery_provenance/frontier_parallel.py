"""Parallel discovery in original-root envelopes; unchanged exact final acceptance.

Each worker owns one dyadic frontier, keeps every ancestor and pays no sibling.
Only grafted original-root checkpoints receive global scope. Run on fixed X.
"""
from pathlib import Path
from fractions import Fraction
from collections import deque
import argparse, concurrent.futures as cf, hashlib, json, os, shutil, subprocess, sys, time

PINS={'I210_214':'3ff485808efe8e73b2b8bb6d012acdc76e6c6fbabb46bd41d4a0f2fe80cde459',
      'II210_214':'d5fe29203e58a4d05c0cda17511343d873cc2b0c788bd4b899f253c9e9d04efb'}

def digest(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()

def write_json(path,obj):
    path=Path(path);tmp=path.with_name(path.name+'.next')
    tmp.write_text(json.dumps(obj,indent=2)+'\n');os.replace(tmp,path)

def run_verify(exe,tree,allow_open=True):
    p=subprocess.run([str(exe),str(tree)]+(['--allow-open'] if allow_open else []),capture_output=True,text=True)
    if p.returncode:raise RuntimeError('Exact rejection: '+p.stderr[-3000:])
    d=json.loads(p.stdout)
    if d['nodes']!=2*d['splits']+1 or d['leaves']+d['open']!=d['splits']+1:raise ValueError('Bad counters')
    return d

def fields(line):
    if not line or not line.endswith(b'\n'):raise ValueError('Missing/truncated tree record')
    f=line.split();tag=f[0]
    if tag==b'S':
        if len(f)!=2:raise ValueError('Malformed split')
        return tag,int(f[1])
    if tag==b'O':
        if len(f)!=1:raise ValueError('Malformed open leaf')
    elif tag==b'R':
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

def patch_focus(source):
    changes=[
      ('long long new_nodes=0,','std::string focus_path;\nlong long new_nodes=0,'),
      ('void resume_tree(const EBox&box,std::istream&in,std::ostream&out){',
       'void resume_tree(const EBox&box,std::istream&in,std::ostream&out,const std::string&path=""){'),
      ('resume_tree(l,in,out);resume_tree(h,in,out);','resume_tree(l,in,out,path+"0");resume_tree(h,in,out,path+"1");'),
      ('}else if(op=="O")refine(box,out);else throw',
       '}else if(op=="O"){if(path.compare(0,focus_path.size(),focus_path)==0)refine(box,out);else out<<"O\\n";}else throw'),
      ('if(argc<3||argc>5)','if(argc<3||argc>6)'),
      ('[MAX_SOLVES]','[MAX_SOLVES] [FOCUS_BINARY_PATH]'),
      ('if(argc==5)max_solves=std::stoll(argv[4]);',
       'if(argc>=5)max_solves=std::stoll(argv[4]);if(argc==6){focus_path=argv[5];if(focus_path.find_first_not_of("01")!=std::string::npos)throw std::runtime_error("bad focus path");}')]
    for old,new in changes:
        if source.count(old)!=1:raise ValueError('Unexpected frozen discovery source: '+old)
        source=source.replace(old,new)
    return source

def prepare_binaries(work,root):
    patch=patch_focus((work/'source/discover.cpp').read_text())
    for name in PINS:
        d=work/'models'/name
        if digest(d/'model.json')!=PINS[name]:raise ValueError('Frozen model changed')
        for fn in ('mc_exact_kernel.hpp','rankone_oracle.hpp','mc_verify.cpp','mc_simplex_dual.hpp'):
            if (d/fn).read_bytes()!=(work/'source'/fn).read_bytes():raise ValueError('Source changed: '+fn)
        src=d/'discover_focus.cpp'
        if src.exists() and src.read_text()!=patch:raise ValueError('Different existing focused driver')
        src.write_text(patch)
        exe=d/'discover_focus'
        if not exe.exists():
            with (root/(name+'_FOCUS_COMPILE.log')).open('w') as log:
                subprocess.run(['g++','-O3','-std=c++17',str(src),'-o',str(exe)],stdout=log,stderr=subprocess.STDOUT,check=True)
    write_json(root/'FOCUS_DRIVER_RECEIPT.json',{'status':'DISCOVERY_SELECTION_ONLY_EXACT_ACCEPTOR_UNCHANGED',
        'source_sha256':digest(work/'source/discover.cpp'),'focused_source_sha256':hashlib.sha256(patch.encode()).hexdigest(),
        'exact_verifier_sha256':digest(work/'source/mc_verify.cpp'),'exact_kernel_sha256':digest(work/'source/mc_exact_kernel.hpp'),
        'rankone_oracle_sha256':digest(work/'source/rankone_oracle.hpp'),'model_pins':PINS})

def prepare_wave(work,wave,inputs,target):
    wave.mkdir();data={n:json.loads((work/'models'/n/'model.json').read_text()) for n in inputs}
    fronts=[];extra={n:{} for n in inputs}
    for n,path in inputs.items():
        fronts+=collect_frontiers(path,data[n],n)
    while len(fronts)<target:
        cand=[(len(e['steps']),i) for i,e in enumerate(fronts) if len(e['steps'])<115]
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
        subprocess.run([str(model/'discover_focus'),str(d/'checkpoint.tree'),str(d/'next.tree'),str(seconds),'1000000',job['focus']],
                       stdout=log,stderr=subprocess.STDOUT,check=True)
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

def main():
    ap=argparse.ArgumentParser();ap.add_argument('task_root',type=Path)
    ap.add_argument('--seconds',type=float,default=7200);ap.add_argument('--workers',type=int,default=40)
    ap.add_argument('--frontiers',type=int,default=80);ap.add_argument('--wave-seconds',type=float,default=900)
    ap.add_argument('--chunk',type=float,default=120);ap.add_argument('--prepare-only',action='store_true')
    ap.add_argument('--models',nargs='+',choices=list(PINS),default=list(PINS))
    a=ap.parse_args();root=a.task_root.resolve();work=root/'working';out=root/'parallel';out.mkdir(exist_ok=True)
    if not 1<=a.workers<=40:raise ValueError('User cap is 40 workers')
    for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
    os.environ['TMPDIR']=str(root/'tmp');os.environ['CPLUS_INCLUDE_PATH']='/root/microscope_ws/controller_v31_review_20260907.cRz00v/deps/usr/include'
    if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
    prepare_binaries(work,out)
    inputs={n:work/'models'/n/'checkpoint.tree' for n in a.models};accepted={}
    current=out/'CURRENT_STATE.json'
    if current.exists():
        accepted=json.loads(current.read_text())['models']
        inputs={n:Path(v['tree']) for n,v in accepted.items() if v['open']>0 and n in a.models}
        for n,v in accepted.items():
            if digest(v['tree'])!=v['tree_sha256'] or v['model_sha256']!=PINS[n]:raise ValueError('Continuation state changed')
    if a.prepare_only:return
    deadline=time.monotonic()+a.seconds;index=len(list(out.glob('wave_*')))
    while inputs and time.monotonic()<deadline:
        index+=1;wave=out/f'wave_{index:03d}';jobs,manifest=prepare_wave(work,wave,inputs,a.frontiers)
        print(json.dumps({'event':'wave_prepared','wave':index,'frontiers':len(jobs),'workers':a.workers}),flush=True)
        execute_wave(work,wave,jobs,a.workers,min(deadline,time.monotonic()+a.wave_seconds),a.chunk)
        results=graft_wave(work,wave,jobs,manifest);accepted.update(results)
        write_json(current,{'status':'ORIGINAL_ROOTS_COMPLETE' if all(v['open']==0 for v in accepted.values()) else 'EXACT_PARTIAL_ORIGINAL_ROOTS',
                    'models':accepted,'last_wave':index,'workers_cap':a.workers,'macro_ledger':'11/15'})
        print(json.dumps({'event':'original_roots_accepted','wave':index,'models':{n:{k:v[k] for k in ('nodes','leaves','open','max_depth')} for n,v in results.items()}}),flush=True)
        inputs={n:Path(v['tree']) for n,v in accepted.items() if v['open']>0 and n in a.models}
    both_complete=len(accepted)==len(PINS) and all(v['open']==0 for v in accepted.values())
    print(json.dumps({'status':'COMPLETE_BOTH_FROZEN_MODELS' if both_complete else 'SOFT_BUDGET_EXACT_CHECKPOINTS_SAVED',
                     'current_state':str(current),'whole_height_claim_requires_both_complete':True}),flush=True)

if __name__=='__main__':main()
