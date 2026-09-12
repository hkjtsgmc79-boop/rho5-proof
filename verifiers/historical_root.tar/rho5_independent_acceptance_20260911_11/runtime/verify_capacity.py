#!/usr/bin/env python3
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import sys,json,random,zipfile,tempfile
from capacity import *
from symmetry import *
from interval_capacity import I,oracle,root_box,wide_beta,wide_prefix
ROOT=Path(__file__).parent

def independent_prefix(u,x,beta):
    # All original +/- L strips retained, instead of the compressed formulas.
    # Row is a*p+b*e<=c. Enumerate every exact boundary intersection.
    rows=[(-1,0,-1),(1,0,2),(0,-1,0),(0,1,1),(1,-beta,1)]
    for ui,xi in zip(u,x):rows += [(xi,-ui,Q(1)),(-xi,ui,Q(1))]
    pts=set()
    for(a,b,c),(d,e,f)in combinations(rows,2):
        det=a*e-b*d
        if det==0:continue
        p=(c*e-b*f)/det;ee=(a*f-c*d)/det
        if all(A*p+B*ee<=C for A,B,C in rows):pts.add((p,ee))
    assert pts
    return max(t[0]for t in pts)

def make_paths(z,out):
    # beta leg, then (p,e) leg, then actual tail leg. Check 1/4,1/2,3/4,1.
    src=list(map(Q,z));dest=out['point_gap'];seq=[]
    a=src[:];a[9]=dest[9]
    b=a[:];b[7]=dest[7];b[8]=dest[8]
    for left,right in ((src,a),(a,b),(b,dest)):
        last=check_complete(left)['F']
        for t in (Q(1,4),Q(1,2),Q(3,4),Q(1)):
            new=[(1-t)*p+t*q for p,q in zip(left,right)]
            value=check_complete(new)['F'];assert value>=last;last=value;seq.append(new)
    return seq

def main():
    rng=random.Random(37001);prefix_checks=0;caps_max=0;image_checks=0;paths_checked=0;symchecks=0
    for _ in range(400):
        u=[Q(rng.randint(-4,4),4)for j in range(3)]
        x=[Q(rng.randint(-4,4),4)for j in range(3)]
        be=Q(rng.randint(0,4),4)
        p,e,caps=prefix_capacity(u,x,be)
        assert p==independent_prefix(u,x,be)
        caps_max=max(caps_max,len(caps));prefix_checks+=1
        # Resolved/unresolved sign charts, including exact zero intervals.
        eps=Q(rng.choice([0,1,2]),100)
        ui=[I(max(-1,a-eps),min(1,a+eps))for a in u]
        xi=[I(max(-1,a-eps),min(1,a+eps))for a in x]
        bii=I(max(0,be-eps),min(1,be+eps))
        res=wide_prefix(ui,xi,bii)
        assert res is not None
        assert res[0].lo<=p<=res[0].hi and res[1].lo<=e<=res[1].hi
        image_checks+=2
    assert caps_max==6
    # Exact B interval endpoint and zero row controls.
    assert beta_interval([Q(0),Q(0),Q(0)],[Q(2),Q(0),Q(0)])is None
    bi=beta_interval([Q(1),Q(-1),Q(0)],[Q(1),Q(-1),Q(0)])
    assert bi[:2]==(Q(0),Q(0))
    assert beta_interval([Q(1),Q(1),Q(0)],[Q(2),Q(-2),Q(0)])is None
    count_beta=3
    for _ in range(160):
        be=Q(rng.randint(0,4),4);v=[Q(rng.randint(-4,4),4)for _ in range(3)]
        q=[Q(rng.randint(-4,4),4)-be*a for a in v]
        bi=beta_interval(v,q);assert bi is not None and bi[0]<=be<=bi[1]
        eps=Q(rng.randint(0,2),100)
        bb=wide_beta([I(max(-1,a-eps),min(1,a+eps))for a in v],[I(a-eps,a+eps)for a in q])
        assert bb is not None and bb.lo<=bi[1]<=bb.hi
        image_checks+=1;count_beta+=1
    # New data are generated from full actual matrices, not disconnected columns.
    low_sources=[]
    for j in range(80):
        k=Q(rng.choice([5,6,7]),10);r=k/2;A=k*Q(rng.randint(-2,0),8);B=k*Q(rng.randint(-2,2),8)
        c=Q(rng.randint(-2,2),8);d=Q(rng.randint(-2,2),8)
        vals=[Q(rng.randint(-2,2),8)for _ in range(12)]
        z=[k,r,-r,A,B,c,d,Q(5,4),Q(3,4),Q(3,4)]+vals+[r/2,2*r/3]
        check_complete(z);out=capacity(extract_frame(z));assert out['status']=='COMPLETE_FIXED_FRAME_MAXIMUM'
        assert out['tail']['F']>=check_complete(z)['F'];low_sources.append(z)
        paths_checked+=len(make_paths(z,out))
    with tempfile.TemporaryDirectory()as tmp:
        with zipfile.ZipFile(ROOT/'dependency/rho5_v36_exact.zip')as z:z.extractall(tmp)
        base=Path(tmp)/'rho5_v36_exact';sys.path.insert(0,str(base))
        import gap_model as old
        controls=json.loads((base/'evidence/proper_B_controls.json').read_text())['controls']
        highs=[]; records=[]
        for obj in controls:
            original=list(map(Q,obj['parameters']))
            for point in (original,diagonal_switch(original),transpose(original),transpose(diagonal_switch(original))):
                out=capacity(extract_frame(point));assert out['status']=='COMPLETE_FIXED_FRAME_MAXIMUM'
                value=check_complete(point)['F'];cap=out['tail']['F']
                assert Q(4132517,1000000)<value<=cap<Q(json.loads((ROOT/'dependency/alpha.json').read_text())['isolating_interval']['lower'])
                old.check_actual(out['point_gap']);highs.append(point)
                for w in make_paths(point,out):old.check_actual(w);paths_checked+=1
                # K really commutes with the canonical capacity map; no such assertion for T.
                kk=diagonal_switch(point);ck=capacity(extract_frame(kk));sw=diagonal_switch(out['point_gap'])
                assert ck['point_gap']==sw
                symchecks+=1
                # All contacts retain exact actual layer semantics under K and T.
                sl0=actual_slacks(point)
                for fn,label_fn in ((diagonal_switch,switch_labels),(transpose,transpose_labels)):
                    sl1=actual_slacks(fn(point))
                    for rs in ('D11+','S11+','O11+','D22-','S22-','O22-'):
                        for s0 in ('D12+','S12+','O12+'):
                            for t0 in ('D21+','S21+','O21+'):
                                dst=label_fn((rs,s0,t0))
                                # K/T exchange second and third providers.
                                assert sl1[dst[0]]==sl0[rs]
                                assert sl1[dst[1]]==sl0[t0]
                                assert sl1[dst[2]]==sl0[s0]
                                symchecks+=3
                # Whole-frame-box scope: check canonical images, not source p/e/r.
                frame=extract_frame(point)
                for radius in (Q(0),Q(1,10**7),Q(1,10**5),Q(1,10**4)):
                    bx=[I(a-radius,a+radius).intersection(root)for a,root in zip(frame,root_box())]
                    assert all(v is not None for v in bx)
                    o=oracle(bx);assert o['status']!='EMPTY'
                    zz=out['point_gap']
                    for a,(l,h)in zip(zz,o['gap_image']):assert Q(l)<=a<=Q(h);image_checks+=1
                records.append({'case':obj['case'],'source_gap':point,'maximum':out})
        (ROOT/'evidence/capacity_controls.json').write_text(json.dumps(encode(records),ensure_ascii=False,indent=2)+'\n')
        (ROOT/'models/example_frame.json').write_text(json.dumps(encode({'frame':extract_frame(highs[0])}),indent=2)+'\n')
    orbits=contact_orbits();assert len(orbits)==18
    wrong=0
    for bad in ([0]*16,[0]*18,[0.0]*17,[True]*17):
        try:capacity(bad)
        except (ValueError,TypeError):wrong+=1
        else:raise AssertionError('bad input accepted')
    result={'status':'V37_CAPACITY_AND_SYMMETRY_COMPONENTS_PASS','prefix_exact_vertex_crosschecks':prefix_checks,
            'maximum_prefix_caps':caps_max,'beta_interval_checks':count_beta,'complete_low_sources':len(low_sources),
            'complete_high_source_images':len(highs),'full_actual_path_points':paths_checked,
            'exact_symmetry_checks':symchecks,'interval_enclosure_checks':image_checks,
            'original_contact_labels':54,'canonical_contact_labels':18,'bad_numeric_inputs_rejected':wrong,
            'whole_B_closed':False,'ledger':'14/15'}
    (ROOT/'evidence/component_result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
