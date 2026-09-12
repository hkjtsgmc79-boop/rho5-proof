#!/usr/bin/env python3
"""Exact geometric description of accepted unpaid boxes; no proof credit added."""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
import argparse,sys,json,hashlib,gzip
ap=argparse.ArgumentParser();ap.add_argument('--package',type=Path,required=True)
ap.add_argument('--state',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
a=ap.parse_args();sys.path.insert(0,str(a.package/'discovery'));import frontier_parallel as fp
state=json.loads(a.state.read_text());alpha=json.loads((a.package/'alpha.json').read_text())
al=Q(alpha['isolating_interval']['lower']);cert=json.loads((a.package/'local_wall_certificate.json').read_text())
rad=Q(cert['inner_radius']);centers=[list(map(Q,x['center'])) for x in cert['cases']]
scale=10**9;outer=Q(cert['outer_radius'])*scale;speed=Q(cert['uniform_speed_cap'])
assert outer.denominator==1 and speed.denominator==1
scaled_centers=[[Q(x)*scale for x in c] for c in centers]
assert all(x.denominator==1 for c in scaled_centers for x in c)
scaled_centers=[[int(x) for x in c] for c in scaled_centers]
a.out.mkdir(parents=True,exist_ok=True);summary={}
for name,rec in state['models'].items():
    assert fp.digest(rec['tree'])==rec['tree_sha256']
    model=json.loads((a.package/'models'/name/'model.json').read_text())
    assert fp.digest(a.package/'models'/name/'model.json')==rec['model_sha256']
    unit=model['root_denominator']*2**128
    fronts=fp.collect_frontiers(rec['tree'],model,name) if rec['open'] else [];assert len(fronts)==rec['open']
    hist=Counter();width_hist=Counter();direct=0;touch=0;deep_direct=0;deep=0;samples=[]
    tail=0;tube=0;ready=0;deep_unready=0
    target=a.out/(name+'_OPEN_FRONTIERS.jsonl.gz')
    with gzip.open(target,'wt') as out:
        for f in fronts:
            depth=len(f['steps']);hist[depth]+=1
            box=[(Q(l,unit),Q(h,unit)) for l,h in zip(f['lo'],f['hi'])]
            safe=box[1][1]-box[2][0]<=al
            tail_safe=2*f['hi'][1]*al.denominator<=al.numerator*unit
            remaining=int(outer)*unit-int(speed)*scale*max(0,f['hi'][1]+f['hi'][2])
            tubes=[]
            if remaining>0:
                sl=[x*scale for x in f['lo']];sh=[x*scale for x in f['hi']]
                tubes=[7+j for j,c in enumerate(scaled_centers) if all(max(abs(sl[i]-c[i]*unit),abs(sh[i]-c[i]*unit))<remaining for i in range(22))]
            cheap_ready=safe or tail_safe or bool(tubes)
            tail+=tail_safe;tube+=bool(tubes);ready+=cheap_ready;deep_unready+=depth>=500 and not cheap_ready
            touching=[i for i,c in enumerate(centers) if all(l<=v+rad and h>=v-rad for (l,h),v in zip(box,c))]
            direct+=safe;touch+=bool(touching);deep+=depth>=500;deep_direct+=safe and depth>=500
            widths=[h-l for l,h in box];widest=max(range(23),key=lambda i:widths[i]);width_hist[model['variables'][widest]]+=1
            r={'steps':f['steps'],'lo':list(map(str,f['lo'])),'hi':list(map(str,f['hi'])),
               'unit':str(unit),'direct_F_safe':safe,'tail_bound_safe':tail_safe,'flow_tube_safe_codes':tubes,
               'touching_local_charts':touching}
            out.write(json.dumps(r,separators=(',',':'))+'\n')
            if len(samples)<8 or (depth>=500 and len(samples)<16):
                samples.append({'path':fp.key(f['steps']),'depth':depth,'bounds':[[str(l),str(h)] for l,h in box],
                                'direct_F_safe':safe,'touching_local_charts':touching,
                                'tail_bound_safe':tail_safe,'flow_tube_safe_codes':tubes,
                                'widest_variable':model['variables'][widest]})
    summary[name]={'open':len(fronts),'tree_sha256':rec['tree_sha256'],
                   'model_sha256':rec['model_sha256'],'depth_histogram':dict(sorted(hist.items())),
                   'at_or_above_search_depth_500':deep,'direct_F_safe_now':direct,
                   'deep_direct_F_safe_now':deep_direct,'touches_one_local_cube':touch,
                   'tail_bound_safe_now':tail,'flow_tube_safe_now':tube,'cheap_alpha_ready_now':ready,
                   'deep_not_cheap_alpha_ready':deep_unready,
                   'cheap_scope':'A5/A6/A7..10; A4 not tested here; this adds no proof credit',
                   'widest_coordinate_histogram':dict(width_hist),'sample_boxes':samples,
                   'all_frontiers_file':str(target),'all_frontiers_sha256':fp.digest(target)}
    print(json.dumps({name:{k:v for k,v in summary[name].items() if k not in ('sample_boxes','depth_histogram')}}),flush=True)
(a.out/'FRONTIER_AUDIT.json').write_text(json.dumps({'status':'EXACT_UNPAID_GEOMETRY_NO_NEW_PROOF_CREDIT',
            'source_state':str(a.state),'models':summary},indent=2)+'\n')
