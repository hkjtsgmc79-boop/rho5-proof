#!/usr/bin/env python3
"""Independent Fraction/native parity, bad-input gates, and fixed-node benchmark."""
from pathlib import Path
from fractions import Fraction as Q
import argparse, copy, gzip, hashlib, json, os, random, time
ROOT=Path(__file__).resolve().parent
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[key]='1'
from interval_capacity import I,oracle as ref_oracle,root_box,ALPHA
from relaxation import margin as ref_margin,rows_and_bounds as ref_rows,verify_leaf as ref_leaf
import tree_protocol as tp
import native_backend as native
import probe

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--audit',type=Path,required=True);parser.add_argument('--accepted',type=Path,required=True);parser.add_argument('--out',type=Path,required=True);args=parser.parse_args()
    if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
    args.out.mkdir();start=time.monotonic();rng=random.Random(480917)
    boxes=[root_box()]+[tp.task_box(i)[0]for i in range(40)]
    with gzip.open(args.audit/'OPEN_FRONTIERS.jsonl.gz','rt')as inp:opens=[json.loads(line)for line in inp]
    for i in range(min(128,len(opens))):boxes.append([I(*v)for v in opens[i*len(opens)//min(128,len(opens))]['box']])
    for j in range(128):
        box=root_box()
        for _ in range(rng.randrange(1,200)):
            axis=rng.randrange(17);box=tp.halve(box,axis)[rng.randrange(2)]
        boxes.append(box)
    epsilon=Q(1,2**80)
    for axis in range(5,14):
        for interval in (I(0),I(-epsilon,epsilon),I(0,epsilon),I(-epsilon,0)):
            box=root_box();iv=interval.intersection(box[axis])
            if iv is not None:box[axis]=iv;boxes.append(box)
    ports=json.loads((ROOT/'evidence/frame_alpha_ports.json').read_text())
    hs=json.loads((ROOT/'evidence/H_arithmetic_controls.json').read_text())
    boxes += [[I(*v)for v in entry['frame_box']]for entry in ports+hs]
    oracle_results=[];ref_seconds=0;native_seconds=0
    for box in boxes:
        now=time.monotonic();expected=ref_oracle(box);ref_seconds+=time.monotonic()-now
        now=time.monotonic();actual=native.oracle(box);native_seconds+=time.monotonic()-now
        if actual!=expected:
            (args.out/'MISMATCH.json').write_text(json.dumps({'box':[v.data()for v in box],'reference':expected,'native':actual},indent=2))
            raise AssertionError('oracle mismatch; inspect MISMATCH.json')
        oracle_results.append(expected)
    row_count=margin_count=0
    selected=[result for result in oracle_results if 'aux_image'in result][::4]
    for result in selected:
        old_rows,old_boxes=ref_rows(result['aux_image']);new_rows,new_boxes=native.rows_and_bounds(result['aux_image'])
        assert old_rows==new_rows and [v.data()for v in old_boxes]==[v.data()for v in new_boxes]
        row_count+=len(old_rows)
        for kind in ('C','H'):
            indices=rng.sample(range(len(old_rows)),7)
            record={'kind':kind,'weights':[[i,rng.randrange(1,10**12)]for i in indices]}
            if kind=='H':record['objective_weight']=10**12
            assert ref_margin(result['aux_image'],record)==native.margin(result['aux_image'],record);margin_count+=1
    for item in hs:
        box=[I(*v)for v in item['frame_box']]
        assert native.verify_leaf(box,item['record'])==ref_leaf(box,item['record'])=='SAFE'
        assert native.margin(ref_oracle(box)['aux_image'],item['record'])==Q(item['margin']);margin_count+=1
    zero=[I(0)]*24
    rows,_=ref_rows(zero)
    row=next(i for i,(co,rhs)in enumerate(rows)if rhs==0 and co.get(23,Q(0))==0)
    for delta in (-epsilon,Q(0),epsilon):
        aux=zero.copy();aux[23]=I(ALPHA+delta);record={'kind':'H','weights':[[row,1]],'objective_weight':1}
        assert ref_margin(aux,record)==native.margin(aux,record)==delta;margin_count+=1
    bad=0
    def reject(fn):
        nonlocal bad
        try:fn()
        except (ValueError,TypeError,KeyError,AssertionError,ZeroDivisionError):bad+=1
        else:raise AssertionError('bad input accepted')
    box=[I(*v)for v in hs[0]['frame_box']];good=hs[0]['record'];row=good['weights'][0][0]
    invalid=[{'kind':'H','weights':[[row,w]],'objective_weight':1}for w in (-1,0,True,1.5,'1')]
    invalid += [{'kind':'H','weights':[[i,1]],'objective_weight':1}for i in (-1,258,True,1.5,'1')]
    invalid += [{'kind':'H','weights':[[row,1]],'objective_weight':t}for t in (-1,0,True,1.5,'1')]
    invalid += [{'kind':'H','weights':[[row,1],[row,1]],'objective_weight':1}, {'kind':'C','weights':[]},
                {'kind':'C','weights':[[row]]}, {'kind':'C','weights':[[row,1]]}]
    for record in invalid:reject(lambda record=record:native.verify_leaf(box,record))
    reject(lambda:native.verify_leaf(root_box(),{'kind':'E'}))
    outside=root_box();outside[0]=I(outside[0].lo-epsilon,outside[0].hi)
    reject(lambda:native.oracle(outside))
    native.install()
    reference_tree=json.loads((ROOT/'evidence/reference_checkpoint.json').read_text())
    old_receipt=json.loads((ROOT/'evidence/reference_checkpoint.json.receipt.json').read_text())
    native_receipt=tp.verify_tree(reference_tree,allow_open=True)
    for key in ('nodes','contradictions','alpha_safe','open','max_depth'):assert native_receipt[key]==old_receipt[key]
    reject(lambda:tp.verify_tree(reference_tree))
    for mutation in (lambda d:d.update(model_sha256='0'*64),lambda d:d.update(root_path='1'),
                     lambda d:d.update(nodes=d['nodes'][:-1]),lambda d:d.update(nodes=d['nodes']+[{'kind':'O'}]),
                     lambda d:d.update(nodes=[{'kind':'Q'}]),
                     lambda d:d.update(nodes=[{'kind':'S','axis':True},{'kind':'O'},{'kind':'O'}])):
        data=copy.deepcopy(reference_tree);mutation(data);reject(lambda data=data:tp.verify_tree(data,allow_open=True))
    # Cross-check actual new/native discoveries with the independent Python arithmetic.
    import relaxation
    benchmarks=[]
    for task in (4,18,26,32):
        tp.verify_leaf=ref_leaf;probe.propose=relaxation.propose
        before=time.monotonic();old=probe.run(task,600,256,args.out/f'reference_{task:02d}.json');old_time=time.monotonic()-before
        native.install();before=time.monotonic();new=probe.run(task,600,256,args.out/f'native_{task:02d}.json');new_time=time.monotonic()-before
        tp.verify_leaf=ref_leaf
        cross=tp.verify_tree(json.loads((args.out/f'native_{task:02d}.json').read_text()),allow_open=True)
        assert all(cross[key]==new[key]for key in ('nodes','contradictions','alpha_safe','open','max_depth'))
        benchmarks.append({'task':task,'attempt_budget':256,'reference_seconds':old_time,'native_seconds':new_time,'reference':old,'native':new,'native_tree_fraction_crosscheck':cross})
    native.install()
    accepted=json.loads(args.accepted.read_text());before=time.monotonic()
    accepted_result=tp.verify_tree(accepted,allow_open=True)
    accepted_seconds=time.monotonic()-before
    parent=json.loads((args.accepted.parent/'BATCH_RECEIPT.json').read_text())
    for key in ('nodes','splits','contradictions','alpha_safe','open','max_depth','whole_B_closed'):assert accepted_result[key]==parent[key]
    result={'status':'B17_NATIVE_EXACT_PARITY_AND_FIXED_NODE_BENCHMARK_PASS','new_research_credit':0,
            'oracle_boxes_compared':len(boxes),'exact_rows_compared':row_count,'margin_comparisons':margin_count,'bad_controls_rejected':bad,
            'oracle_reference_seconds':ref_seconds,'oracle_native_seconds':native_seconds,'fixed_node_benchmarks':benchmarks,
            'prior_full_original_tree_native_replay':accepted_result,'prior_tree_native_replay_seconds':accepted_seconds,
            'prior_tree_sha256':hashlib.sha256(args.accepted.read_bytes()).hexdigest(),
            'source_sha256':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()for name in ('b17_native.cpp','b17_native_data.hpp','native_backend.py','libb17_native.so')},
            'total_seconds':time.monotonic()-start,'macro_ledger':'14/15'}
    (args.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
