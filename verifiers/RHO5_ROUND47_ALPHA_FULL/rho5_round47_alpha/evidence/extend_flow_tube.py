#!/usr/bin/env python3
"""Certify a larger source domain using the already certified wall-flow bounds."""
from pathlib import Path
import argparse,json,hashlib,shutil,subprocess,sys
ap=argparse.ArgumentParser();ap.add_argument('root',type=Path);a=ap.parse_args()
own=a.root.resolve();src=own/'working_direct_f';dst=own/'working_flow_tube'
state=json.loads((src/'campaign_low_alpha/CURRENT_STATE.json').read_text())
assert set(state['models'])=={'I_LOW_ALPHA','II_LOW_ALPHA'}
assert not dst.exists()
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def copy(f,g):g.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,g)
def dump(p,d):p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
manifest=json.loads((src/'MANIFEST.json').read_text())
for n,h in manifest['files'].items():
    assert digest(src/n)==h,n
    copy(src/n,dst/n)
copy(src/'MANIFEST.json',dst/'reference/DIRECT_F_PARENT_MANIFEST.json')
for n,rec in state['models'].items():
    assert digest(rec['tree'])==rec['tree_sha256']
    copy(src/'models'/n/'model.json',dst/'reference/direct_f_parent_models'/f'{n}.json')
    copy(Path(rec['tree']),dst/'models'/n/'checkpoint.tree')
dump(dst/'reference/DIRECT_F_PARENT_STATE.json',state)
oldrule=json.loads((dst/'DIRECT_F_RULE.json').read_text());rule=dict(oldrule)
rule.update(flow_tube_codes=[7,8,9,10],flow_tube_domain='max_i|z_i-center_i| + speed*max(0,r+w) < outer_radius',
            flow_tube_certificate_sha256=digest(dst/'local_wall_certificate.json'),
            flow_tube_meaning='F <= alpha - uniform_height_gain*(r+w), using the original outer-box flow certificate')
dump(dst/'DIRECT_F_RULE.json',rule)
(dst/'FLOW_TUBE_THEOREM.md').write_text('''# CQG Round47: larger domains of the verified physical wall flow

Write R=1/1250, s=3 and delta=r+w. The existing V35 certificate verifies, on
each complete outer cube about c_j, an invertible 21-coordinate slack Jacobian,
speed ||J^{-1}e_delta||_infinity < s, height gain at least 1/10, all 79 unused
physical slacks strictly positive and all 16 transformed wall endpoint R0
guards strictly positive. The exact certificate and alpha definition are
unchanged and are reverified before generating any accepting binary.

Theorem. Every complete physical X source z in

    ||z-c_j||_infinity + s*(r+w) < R

satisfies F(z) <= alpha-(r+w)/10. Physicality supplies delta>=0; p is fixed
along the associated flow and may vary between sources. There are no new
contact, rank, receiver sign, cofactor sign, or gamma assumptions.

Proof. Run exactly the V35 ODE y_dot=-J(y,p)^{-1}e_delta. The 20 selected
physical slack values remain fixed and delta(t)=delta(0)-t. Up to t=delta(0),
the distance to c_j is at most ||z-c_j||_infinity+s*delta(0)<R. Thus the solution
stays a positive distance from the outer boundary, with positive pivots and
all unselected slacks positive. Smooth finite-dimensional ODE continuation
extends it to delta=0. F gains at least delta(0)/10. Only at that endpoint apply
the inherited signed tail permutation; all complete strict R0 guards hold on
the entire transformed outer cube. The frozen R0 theorem gives F_end<=alpha.
The case delta(0)=0 is the same endpoint argument with zero time. This proves
the claim. No off-wall tail permutation or numerical integration is used.

For an exact ancestral box B, let D=max over i of max(|lo_i-c_i|,|hi_i-c_i|),
and let U=max(0,r_upper+w_upper). Every actual physical source in B satisfies
||z-c||<=D and 0<=delta<=U. Hence the exact strict comparison D+s*U<R
certifies the entire source-conditioned box. Coordinates are the first 22
native coordinates; the extra actual G remains bound by the unchanged model
rows and is irrelevant to this geometric estimate. Codes A7..A10 correspond
to j=0..3. They are alpha safety leaves, never contradiction leaves.

The four old inner boxes are included: D<=1/10000 and U<=2/10000 imply
D+s*U<=7/10000<R. The new domains can also contain sources farther from the
center when their actual wall distance is small. This is a stronger use of
the existing outer-box certificate, not an unverified increase of that box.

All original root bounds and necessary rows, including r=k, gamma, the actual
low transpose and G, remain unchanged. Model metadata explicitly binds the
original V35 parent and the immediately preceding direct-F version. No global
coverage is inferred until both complete original-root trees are paid and
freshly replayed. Existing zero/boundary and macro transport results retain
their original scope; macro credit is left to the controller.
''')
def change(n,old,new):
    p=dst/n;t=p.read_text();assert t.count(old)==1,(n,old,t.count(old));p.write_text(t.replace(old,new))
change('build_models.py',"data['source_version']='V35_CQG_ROUND47_DIRECT_F_2026-09-08'", "data['source_version']='V35_CQG_ROUND47_FLOW_TUBE_2026-09-08'")
change('build_models.py',"    return data", "    previous=ROOT/'reference/direct_f_parent_models'/f'{typ}_LOW_ALPHA.json'\n    old=json.loads(previous.read_text())\n    if any(old[k]!=data[k] for k in ('variables','root_numerators','root_denominator','rows','pairs','K','J','type','branch','target')):raise ValueError('Direct F parent geometry changed')\n    data['previous_version_model_sha256']=hashlib.sha256(previous.read_bytes()).hexdigest()\n    for i in range(4):data['legal_safe_terminal_codes'][str(i+7)]='certified_flow_tube_'+str(i)\n    return data")
change('alpha_ports.py',' if code==6:', ''' if 7<=code<=10:
  center=list(map(Q,cert['cases'][code-7]['center']))
  radius=Q(cert['outer_radius']);speed=Q(cert['uniform_speed_cap'])
  distance=max(max(abs(l-c),abs(h-c)) for (l,h),c in zip(box,center))
  wall_upper=max(Q(0),box[1][1]+box[2][1])
  return distance+speed*wall_upper<radius
 if code==6:''')
change('alpha_ports.py',' for i in range(7):',' for i in range(11):')
change('alpha_ports.py',repr(oldrule),repr(rule))
change('alpha_ports.py','constexpr long long AC_SCALE=1000000000LL;', 'constexpr long long AC_SCALE=1000000000LL;\nconstexpr long long AC_OUTER=800000LL;\nconstexpr long long AC_SPEED=3LL;')
change('alpha_ports.py'," if model.get('additional_alpha_rule_sha256')", " if Q(cert['outer_radius'])!=Q(1,1250) or Q(cert['uniform_speed_cap'])!=3:raise ValueError('Unsupported flow constants')\n if rule['flow_tube_certificate_sha256']!=hashlib.sha256((ROOT/'local_wall_certificate.json').read_bytes()).hexdigest():raise ValueError('Unbound outer certificate')\n if model.get('additional_alpha_rule_sha256')")
change('alpha_ports.py',' if(code==6)return', ''' if(code>=7&&code<=10){
  int j=code-7;Big distance=0;Big du=b.hi[1]+b.hi[2];if(du<0)du=0;
  for(int i=0;i<22;i++){
   Big a=Big(b.lo[i]*AC_SCALE)-Big(AC_CENTER[j][i])*UNIT;if(a<0)a=-a;
   Big z=Big(b.hi[i]*AC_SCALE)-Big(AC_CENTER[j][i])*UNIT;if(z<0)z=-z;
   if(a>distance)distance=a;if(z>distance)distance=z;
  }
  return distance+Big(AC_SPEED)*AC_SCALE*du<Big(AC_OUTER)*UNIT;
 }
 if(code==6)return''')
change('alpha_ports.py','for(int c=0;c<7;c++)','for(int c=0;c<11;c++)')
change('source/mc_verify.cpp','std::array<long long,7>safe_counts','std::array<long long,11>safe_counts')
change('source/mc_verify.cpp','code>6','code>10')
change('source/mc_verify.cpp','safe_counts[0]+safe_counts[1]+safe_counts[2]+safe_counts[3]', 'safe_counts[0]+safe_counts[1]+safe_counts[2]+safe_counts[3]+safe_counts[7]+safe_counts[8]+safe_counts[9]+safe_counts[10]')
change('source/mc_verify.cpp','<<safe_counts[6]<<', '<<safe_counts[6]<<",\\\"flow_tube_leaves\\\":"<<(safe_counts[7]+safe_counts[8]+safe_counts[9]+safe_counts[10])<<')
change('discovery/frontier_parallel.py','not 0<=int(f[1])<=6','not 0<=int(f[1])<=10')
change('tests/alpha_oracle_probe.cpp','c<7','c<11')
change('verify_alpha_ports.py','range(7)','range(11)')
change('verify_alpha_ports.py',"('unknown_safe_code','A 7\\n')","('unknown_safe_code','A 11\\n')")
change('verify_alpha_ports.py',"'code_comparisons':len(boxes)*7","'code_comparisons':len(boxes)*11")
change('verify_alpha_ports.py',' for _ in range(48):', ''' # Tube strict boundary, at the boundary and its adjacent integer grid points.
 for case in cert['cases']:
  center=list(map(Q,case['center']));outer=Q(cert['outer_radius'])
  for du in (Q(0),Q(1,100000)):
   for shift in (-1,0,1):
    z=list(center);z[2]+=du;z[7]+=outer-3*du+Q(shift,unit)
    boxes.append(interval_box(z,0))
 for _ in range(48):''')
change('export_light.py',"'reference/parent_models/*.json'", "'reference/parent_models/*.json','reference/direct_f_parent_models/*.json'")
change('export_light.py',"'DIRECT_F_THEOREM.md'", "'DIRECT_F_THEOREM.md','FLOW_TUBE_THEOREM.md'")
# Within one process, identical verifier bytes and tree bytes already accepted
# need not be replayed again when merely copied into an unchanged wave envelope.
# The final cold semantic verifier is a fresh subprocess and never uses this cache.
change('discovery/frontier_parallel.py','def run_verify(exe,tree,allow_open=True):', '''_VERIFY_CACHE={}
def run_verify(exe,tree,allow_open=True):
    cache_key=(digest(exe),digest(tree),bool(allow_open))
    if cache_key in _VERIFY_CACHE:
        return dict(_VERIFY_CACHE[cache_key])''')
change('discovery/frontier_parallel.py','    return d\n\ndef fields', '    _VERIFY_CACHE[cache_key]=dict(d)\n    return d\n\ndef fields')
program='''from pathlib import Path
import json
from build_models import make_model,headers
root=Path.cwd()
for n in ('I_LOW_ALPHA','II_LOW_ALPHA'):
 p=root/'models'/n;old=json.loads((p/'model.json').read_text())
 new=make_model(old['K'],old['J'],old['type'],old['branch'])
 assert all(new[k]==old[k] for k in ('root_numerators','root_denominator','variables','pairs','rows','K','J','branch','target','alpha_definition_sha256','alpha_ports_certificate_sha256'))
 headers(new,p)
 (p/'model.json').write_text(json.dumps(new,indent=2)+'\\n')
'''
r=subprocess.run([sys.executable,'-c',program],cwd=dst,text=True,capture_output=True)
assert r.returncode==0,r.stdout+r.stderr
dump(dst/'MANIFEST.json',{'schema':'CQG_V35_FLOW_TUBE_EXTENSION_STATIC_V1','scope':'same V35 original roots, A6 direct F plus A7..10 certified wall-flow tubes',
    'files':{str(p.relative_to(dst)):digest(p) for p in sorted(dst.rglob('*')) if p.is_file() and '__pycache__' not in p.parts}})
receipt={'status':'FLOW_TUBE_RULE_VERSION_BUILT_REPLAY_REQUIRED','working':str(dst),
         'parent_source':str(src),'original_root_boxes_and_necessary_rows_unchanged':True,
         'parent_models':{n:r['model_sha256'] for n,r in state['models'].items()},
         'new_models':{n:digest(dst/'models'/n/'model.json') for n in state['models']},
         'starting_trees':{n:r['tree_sha256'] for n,r in state['models'].items()},
         'rule_sha256':digest(dst/'DIRECT_F_RULE.json'),'factor_graph_sha256':digest(dst/'source/factor_graph.hpp')}
dump(own/'FLOW_TUBE_EXTENSION_ADOPTION.json',receipt);print(json.dumps(receipt,indent=2))
