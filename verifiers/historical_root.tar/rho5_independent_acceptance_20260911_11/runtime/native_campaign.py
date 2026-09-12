#!/usr/bin/env python3
"""One writer; exact task receipts compose through the frozen 40-part partition.
Final frozen delivery still requires an actual whole-root replay and cold replay.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as Q
import argparse, datetime, fcntl, hashlib, json, multiprocessing, os, shutil, subprocess, sys, time
from concurrent.futures import ProcessPoolExecutor,as_completed
ROOT=Path(__file__).resolve().parent;OWN=ROOT.parent
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[key]='1'
os.environ['TMPDIR']=str(OWN/'tmp')
import tree_protocol as tp
from native_probe import run as run_task,structure,identity

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def write(path,data):Path(path).write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
def event(status,**data):
    out={'status':status,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**data}
    write(OWN/'HIGH_VALUE_CURRENT_STATUS.json',out);print(json.dumps(out),flush=True)

def stats(data):
    counts=Counter();depths=[0];maximum=0;volume=Q(0)
    for node in data['nodes']:
        depth=depths.pop();maximum=max(maximum,depth);kind=node['kind'];counts[kind]+=1
        if kind=='S':depths.extend([depth+1,depth+1])
        elif kind=='O':volume+=Q(1,2**depth)
    assert not depths
    return {'nodes':len(data['nodes']),'splits':counts['S'],'open':counts['O'],'max_depth':maximum,
            'kinds':dict(counts),'normalized_open_box_volume':str(volume)}

def compose(directory,destination):
    tp.verify_partition();part=json.loads((ROOT/'models/PARTITION40.json').read_text())
    tasks={};receipts=[];current_identity=identity()
    for leaf in part['leaves']:
        task=leaf['task'];path=directory/f'task_{task:02d}.json';data=json.loads(path.read_text());structure(data,task)
        receipt=json.loads(path.with_suffix(path.suffix+'.receipt.json').read_text())
        if receipt.get('tree_sha256')!=sha(path)or receipt.get('native_identity')!=current_identity:raise ValueError('unbound accepted task receipt')
        if receipt.get('model_sha256')!=data['model_sha256']or receipt.get('root_path')!=data['root_path']:raise ValueError('receipt ownership mismatch')
        actual=stats(data)
        for key in ('nodes','splits','open','max_depth'):
            if receipt[key]!=actual[key]:raise ValueError('structural receipt mismatch '+key)
        if receipt['contradictions']+receipt['alpha_safe']+receipt['open']!=receipt['splits']+1:raise ValueError('leaf count mismatch')
        if actual['kinds'].get('C',0)>receipt['contradictions']or actual['kinds'].get('H',0)>receipt['alpha_safe']:raise ValueError('C/H classification mismatch')
        tasks[leaf['path']]=data['nodes'];receipts.append(receipt)
    nodes=[]
    def visit(path):
        if path in tasks:nodes.extend(tasks[path]);return
        nodes.append({'kind':'S','axis':part['splits'][path]});visit(path+'0');visit(path+'1')
    visit('');data=tp.empty_tree();data['nodes']=nodes;structure(data,None)
    destination.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
    result=stats(data)
    result.update({'contradictions':sum(r['contradictions']for r in receipts),'alpha_safe':sum(r['alpha_safe']for r in receipts),
                   'status':'COMPOSITIONAL_EXACT_PARTIAL'if result['open']else'READY_FOR_STRICT_FROZEN_ROOT',
                   'whole_B_closed':False,'final_full_root_replay_required':True,'tree_sha256':sha(destination),
                   'model_sha256':data['model_sha256'],'partition_sha256':sha(ROOT/'models/PARTITION40.json'),
                   'native_identity':current_identity,'task_tree_hashes':{r['task']:r['tree_sha256']for r in receipts},
                   'acceptance_basis':'Each task exactly accepted once; complete frozen partition, task model/path/tree/source bindings and structural coverage checked during composition',
                   'macro_ledger':'14/15'})
    return result

def adopt():
    parent=OWN/'native_wave_02';control=json.loads((OWN/'high_value_controls/RESULT.json').read_text())
    assert control['status']=='B17_HIGH_VALUE_V1_EXACT_CONTROLS_PASS'
    assert control['native_identity']==identity()
    parent_receipt=json.loads((parent/'WAVE_RECEIPT.json').read_text())
    assert parent_receipt['tree_sha256']==sha(parent/'B17_COMPOSED_ROOT.json')
    directory=ROOT/'campaign_native';directory.mkdir();current_id=identity()
    for task in range(40):
        name=f'task_{task:02d}.json';shutil.copy2(parent/name,directory/name)
        data=json.loads((directory/name).read_text());structure(data,task)
        assert all('enclosure'not in n for n in data['nodes'])
        receipt=json.loads((parent/(name+'.receipt.json')).read_text())
        assert receipt['tree_sha256']==sha(directory/name)==parent_receipt['task_tree_hashes'][str(task)]
        assert receipt['native_identity']==parent_receipt['native_identity']
        receipt.update(stats(data));receipt.update({'task':task,'root_path':data['root_path'],'tree_sha256':sha(directory/name),
            'model_sha256':data['model_sha256'],'native_identity':current_id,
            'adopted_from_accepted_parent':parent_receipt['tree_sha256'],
            'parent_native_identity':parent_receipt['native_identity'],'adoption_adds_no_coverage':True,
            'acceptance_basis':'Inherited untagged leaves retain old semantics; exact task scan on continuation; frozen whole root scan required'})
        write(directory/(name+'.receipt.json'),receipt)
    merged=directory/'B17_COMPOSED_ROOT.json';result=compose(directory,merged)
    assert merged.read_bytes()==(parent/'B17_COMPOSED_ROOT.json').read_bytes()
    result.update({'status':'B17_HIGH_VALUE_ADOPTION_BYTE_IDENTICAL_FULL_ROOT','new_coverage_credit':0,
                   'parent_tree_sha256':parent_receipt['tree_sha256'],'compatibility_controls_sha256':sha(OWN/'high_value_controls/RESULT.json')})
    write(OWN/'HIGH_VALUE_ADOPTION.json',result);print(json.dumps(result,indent=2))

def worker(arguments):
    task,seconds,nodes,path,depth=arguments
    try:return {'task':task,'result':run_task(task,seconds,nodes,path,depth)}
    except Exception as error:return {'task':task,'error':str(error),'status':'FAILED_PREVIOUS_ACCEPTED_TREE_PRESERVED'}

def run(args):
    with (ROOT/'.campaign.lock').open('a')as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        manifest=json.loads((ROOT/'HIGH_VALUE_SOURCE_MANIFEST.json').read_text())
        for name,digest in manifest['files'].items():assert sha(ROOT/name)==digest,name
        start=time.monotonic();directory=ROOT/'campaign_native';snapshot=OWN/f'high_value_wave_{args.wave:02d}'
        snapshot.mkdir();event('NATIVE_B17_DISCOVERY_RUNNING',wave=args.wave,workers=args.workers,seconds_per_task=args.seconds,nodes_per_task=args.nodes,max_depth=args.max_depth)
        parameters=[(i,args.seconds,args.nodes,str(directory/f'task_{i:02d}.json'),args.max_depth)for i in range(40)]
        records=[]
        with ProcessPoolExecutor(max_workers=args.workers,mp_context=multiprocessing.get_context('spawn'))as pool:
            futures=[pool.submit(worker,p)for p in parameters]
            for future in as_completed(futures):
                record=future.result();records.append(record);print(json.dumps(record),flush=True)
                write(snapshot/'TASK_RESULTS.json',sorted(records,key=lambda x:x['task']))
        if any('result'not in r for r in records):raise RuntimeError('Task failed; inspect TASK_RESULTS.json')
        for path in directory.glob('task_*.json*'):
            if path.name.endswith('.pending'):continue
            shutil.copy2(path,snapshot/path.name)
        result=compose(snapshot,snapshot/'B17_COMPOSED_ROOT.json')
        result.update({'wave':args.wave,'workers':args.workers,'seconds_per_task':args.seconds,'nodes_per_task':args.nodes,
                       'wall_seconds':time.monotonic()-start,'new_attempts':sum(r['result']['new_attempts']for r in records),
                       'task_results':records,'all_tasks_have_independent_exact_acceptance':True})
        write(snapshot/'WAVE_RECEIPT.json',result)
        event('NATIVE_B17_WAVE_ACCEPTED',wave=args.wave,receipt=str(snapshot/'WAVE_RECEIPT.json'),
              **{k:result[k]for k in ('nodes','contradictions','alpha_safe','open','max_depth','new_attempts','wall_seconds','normalized_open_box_volume')})

def main():
    p=argparse.ArgumentParser();p.add_argument('--adopt',action='store_true');p.add_argument('--run',action='store_true');p.add_argument('--wave',type=int,default=1);p.add_argument('--workers',type=int,default=40);p.add_argument('--seconds',type=float,default=120);p.add_argument('--nodes',type=int,default=8192);p.add_argument('--max-depth',type=int,default=96);a=p.parse_args()
    if not 1<=a.workers<=40 or a.nodes<1 or a.seconds<=0:raise ValueError('invalid budget')
    if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
    if a.adopt:
        with (ROOT/'.campaign.lock').open('a')as lock:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);adopt()
    elif a.run:
        try:run(a)
        except Exception as error:event('NATIVE_FAILED_REVIEW_REQUIRED',wave=a.wave,error=str(error));raise
    else:
        log=OWN/f'HIGH_VALUE_WAVE_{a.wave:02d}.log'
        # The launcher already has absolute nice10; the child does not increment it.
        with log.open('x')as stream:
            process=subprocess.Popen([sys.executable,str(Path(__file__).resolve()),'--run','--wave',str(a.wave),'--workers',str(a.workers),'--seconds',str(a.seconds),'--nodes',str(a.nodes),'--max-depth',str(a.max_depth)],cwd=ROOT,stdin=subprocess.DEVNULL,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
        result={'status':'NATIVE_B17_WAVE_LAUNCHED','pid':process.pid,'log':str(log),'wave':a.wave,'workers':a.workers,'seconds_per_task':a.seconds,'nodes_per_task':a.nodes}
        write(OWN/f'HIGH_VALUE_WAVE_{a.wave:02d}_LAUNCH.json',result);print(json.dumps(result,indent=2))
if __name__=='__main__':main()
