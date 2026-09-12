#!/usr/bin/env python3
"""Actual-frontier Fraction/native parity, containment, compatibility and tag gates."""
from pathlib import Path
from fractions import Fraction as Q
import argparse,copy,hashlib,json,os,random,time
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[key]='1'
import native_backend as nb
import high_value_reference as ref
from interval_capacity import I,root_box,GAMMA
from capacity import extract_frame
from relaxation import margin as ref_margin
import tree_protocol as tp
from native_probe import run,structure,identity
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser();p.add_argument('--prior',type=Path,required=True);p.add_argument('--cases',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();a.out.mkdir()
    if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
    start=time.monotonic();os.environ['B17_NATIVE_LIB']=str(a.prior/'libb17_native.so');old=nb.Engine()
    os.environ['B17_NATIVE_LIB']=str(ROOT/'libb17_native.so');new=nb.Engine();nb._engine=new
    cases=json.loads(a.cases.read_text());boxes=[root_box()]+[tp.task_box(i)[0]for i in range(40)]
    boxes += [[I(*v)for v in c['box']]for c in cases]
    rng=random.Random(481010);eps=Q(1,2**80)
    for axis in range(5,14):
        for iv in (I(0),I(-eps,eps),I(0,eps),I(-eps,0)):
            b=root_box();b[axis]=b[axis].intersection(iv)
            if b[axis] is not None:boxes.append(b)
    for _ in range(64):
        b=root_box()
        for _ in range(rng.randrange(1,150)):b=tp.halve(b,rng.randrange(17))[rng.randrange(2)]
        boxes.append(b)
    physical=0
    for rec in json.loads((ROOT/'evidence/capacity_controls.json').read_text()):
        z=list(map(Q,rec['maximum']['point_gap']));r=z[1];s=r-z[22];t=r-z[23];F=r+s*t/r
        if F<GAMMA:continue
        aux=[z[0],r,s,t,*z[3:10],*z[10:22],F];frame=extract_frame(z)
        for radius in (Q(0),Q(1,100000),Q(1,1000)):
            b=[I(v-radius,v+radius).intersection(root)for v,root in zip(frame,root_box())]
            out=nb.oracle(b,enclosure=nb.ENCLOSURE);assert out['status']!='EMPTY'
            for value,(lo,hi)in zip(aux,out['aux_image']):assert Q(lo)<=value<=Q(hi)
            boxes.append(b);physical+=1
    parity=old_leaves=new_leaves=stripped_rejected=0
    def reject(fn):
        try:fn()
        except (ValueError,TypeError,KeyError,AssertionError,ZeroDivisionError):return
        raise AssertionError('invalid control accepted')
    for b in boxes:
        encoded=[v.data()for v in b]
        assert old.request({'mode':'oracle','box':encoded})==nb.oracle(b)
        for ports in (False,True):
            expected=ref.oracle(b,local_ports=ports);actual=nb.oracle(b,local_ports=ports,enclosure=nb.ENCLOSURE)
            if expected!=actual:
                (a.out/'MISMATCH.json').write_text(json.dumps({'box':encoded,'reference':expected,'native':actual},indent=2));raise AssertionError('high-value parity mismatch')
        parity+=1
    for c in cases:
        b=c['box'];record=c['old_certificate']
        if record:
            assert old.request({'mode':'leaf','box':b,'record':record})['leaf_status']==nb.verify_leaf(b,record)==ref.verify_leaf(b,record);old_leaves+=1
        record=c['proposed_certificate']
        if record:
            record={**record,'enclosure':nb.ENCLOSURE}
            assert nb.verify_leaf(b,record)==ref.verify_leaf(b,record);new_leaves+=1
            if record['kind']in('C','H'):
                aux=nb.oracle(b,enclosure=nb.ENCLOSURE)['aux_image']
                assert nb.margin(aux,record)==ref_margin(aux,record)==Q(c['proposed_margin'])
                stripped={k:v for k,v in record.items()if k!='enclosure'}
                try:nb.verify_leaf(b,stripped)
                except ValueError:stripped_rejected+=1
    assert stripped_rejected>0, 'must demonstrate new certificates cannot silently use old semantics'
    bad=0
    for enclosure in ('unknown','',None,True,1,{},[]):
        rec={'kind':'E','enclosure':enclosure}
        reject(lambda:nb.verify_leaf(root_box(),rec));reject(lambda:ref.verify_leaf(root_box(),rec));bad+=2
    reject(lambda:nb.engine().request({'mode':'leaf','box':nb.box_data(root_box()),'record':{'kind':'E'},'enclosure':nb.ENCLOSURE}));bad+=1
    for c in json.loads((ROOT/'evidence/H_arithmetic_controls.json').read_text()):
        assert nb.verify_leaf(c['frame_box'],c['record'])==ref.verify_leaf(c['frame_box'],c['record'])=='SAFE';old_leaves+=1
    for c in json.loads((ROOT/'evidence/frame_alpha_ports.json').read_text()):
        record={'kind':'E','enclosure':nb.ENCLOSURE}
        assert nb.verify_leaf(c['frame_box'],record)==ref.verify_leaf(c['frame_box'],record)=='SAFE';new_leaves+=1
    searches=[]
    for task in (4,32):
        path=a.out/f'task_{task:02d}.json';r=run(task,120,128,path)
        tp.verify_leaf=ref.verify_leaf;cross=tp.verify_tree(json.loads(path.read_text()),allow_open=True)
        for k in ('nodes','contradictions','alpha_safe','open','max_depth'):assert r[k]==cross[k]
        before=path.read_bytes();reject(lambda:run(task+1,120,1,path));assert before==path.read_bytes();bad+=1
        d=json.loads(path.read_text());d['nodes']=d['nodes'][:-1];reject(lambda:structure(d,task));bad+=1
        searches.append({'task':task,'native':r,'fraction':cross})
    result={'status':'B17_HIGH_VALUE_V1_EXACT_CONTROLS_PASS','oracle_boxes':parity,'local_ports_variants_per_box':2,
            'physical_maximum_containment_checks':physical,'old_leaf_compatibility':old_leaves,'new_leaf_fraction_checks':new_leaves,
            'new_certificates_rejected_without_tag':stripped_rejected,'bad_controls_rejected':bad,'searches':searches,
            'native_identity':identity(),'library_sha256':sha(ROOT/'libb17_native.so'),'prior_library_sha256':sha(a.prior/'libb17_native.so'),
            'source_sha256':{n:sha(ROOT/n)for n in ('b17_native.cpp','native_backend.py','high_value_contraction.py','high_value_reference.py','HIGH_VALUE_RULE.json')},
            'seconds':time.monotonic()-start,'new_proof_credit':0,'whole_B_closed':False,'macro_ledger':'14/15'}
    (a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
