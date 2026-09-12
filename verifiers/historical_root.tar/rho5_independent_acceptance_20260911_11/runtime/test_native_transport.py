#!/usr/bin/env python3
"""Only transport/fair scheduling changed: compare native fields and reference replay."""
from pathlib import Path
import argparse, copy, hashlib, json, os, time
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[key]='1'
from interval_capacity import I,root_box
import tree_protocol as tp
from relaxation import verify_leaf as ref_leaf
import native_backend as nb
from native_probe import run,structure
ROOT=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser();p.add_argument('--prior',type=Path,required=True);p.add_argument('--audit',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();a.out.mkdir()
    if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
    os.environ['B17_NATIVE_LIB']=str(a.prior/'libb17_native.so');old=nb.Engine()
    os.environ['B17_NATIVE_LIB']=str(ROOT/'libb17_native.so');new=nb.Engine();nb._engine=new
    samples=json.loads((a.audit/'SAMPLE_CONTROLS.json').read_text())
    controls=[(rec['box'],rec.get('certificate'))for rec in samples]
    controls += [(rec['frame_box'],rec['record'])for rec in json.loads((ROOT/'evidence/H_arithmetic_controls.json').read_text())]
    tree=json.loads((ROOT/'evidence/reference_checkpoint.json').read_text());stack=[root_box()]
    for node in tree['nodes']:
        b=stack.pop()
        if node['kind']=='S':l,r=tp.halve(b,node['axis']);stack.extend([r,l])
        elif node['kind']in('C','E','H'):controls.append(([x.data()for x in b],node))
    tested=0
    for box,record in controls:
        before=old.request({'mode':'oracle','box':box});after=new.request({'mode':'oracle','box':box});assert before==after
        before=old.request({'mode':'prepare','box':box});after=new.request({'mode':'prepare','box':box})
        for key in ('status','rows_float','rhs_float','center','half'):assert before.get(key)==after.get(key)
        if record:
            before=old.request({'mode':'leaf','box':box,'record':record});after=new.request({'mode':'leaf','box':box,'record':record})
            for key in ('status','leaf_status','margin'):assert before.get(key)==after.get(key)
        tested+=1
    results=[]
    for task in (4,32):
        path=a.out/f'task_{task:02d}.json'
        first=run(task,120,128,path);second=run(task,120,128,path)
        tp.verify_leaf=ref_leaf;cross=tp.verify_tree(json.loads(path.read_text()),allow_open=True)
        for key in ('nodes','contradictions','alpha_safe','open','max_depth'):assert cross[key]==second[key]
        snapshot=path.read_bytes()
        try:run(task+1,120,16,path)
        except ValueError:pass
        else:raise AssertionError('wrong-owner resume accepted')
        assert path.read_bytes()==snapshot
        results.append({'task':task,'first':first,'second':second,'reference_replay':cross,'wrong_owner_rejected_previous_bytes_preserved':True})
    invalid=copy.deepcopy(tree);invalid['nodes']=invalid['nodes'][:-1]
    try:structure(invalid,None)
    except ValueError:pass
    else:raise AssertionError('truncated transport accepted')
    result={'status':'B17_COMPACT_IO_AND_FAIR_FRONTIER_CONTROLS_PASS','compared_frames':tested,
            'scope':'Serialization omits unused fields only; exact interval and margin functions unchanged',
            'prior_library_sha256':hashlib.sha256((a.prior/'libb17_native.so').read_bytes()).hexdigest(),
            'current_library_sha256':hashlib.sha256((ROOT/'libb17_native.so').read_bytes()).hexdigest(),
            'source_sha256':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()for name in ('b17_native.cpp','native_backend.py','native_probe.py')},
            'search_controls':results,'new_research_credit':0,'whole_B_closed':False,'ledger':'14/15'}
    (a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
