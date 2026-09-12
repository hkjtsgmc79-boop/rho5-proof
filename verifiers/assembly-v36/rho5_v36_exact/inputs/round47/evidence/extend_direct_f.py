#!/usr/bin/env python3
"""Build a separately versioned proof-rule extension; never edit the frozen run."""
from pathlib import Path
import argparse,json,hashlib,shutil,subprocess,sys

ap=argparse.ArgumentParser();ap.add_argument('root',type=Path);a=ap.parse_args()
own=a.root.resolve();src=own/'working';dst=own/'working_direct_f'
state=json.loads((src/'campaign_low_alpha/CURRENT_STATE.json').read_text())
assert set(state['models'])=={'I_LOW_ALPHA','II_LOW_ALPHA'}
assert not dst.exists(), 'new version must not overwrite an existing run'
manifest=json.loads((src/'MANIFEST.json').read_text())
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def copy(f,g):g.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,g)
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
for n,h in manifest['files'].items():
    assert digest(src/n)==h,n
    copy(src/n,dst/n)
copy(src/'MANIFEST.json',dst/'reference/V35_ORIGINAL_MANIFEST.json')
copy(src/'build_models.py',dst/'build_models_original.py')
for n,rec in state['models'].items():
    assert digest(rec['tree'])==rec['tree_sha256']
    copy(src/'models'/n/'model.json',dst/'reference/parent_models'/f'{n}.json')
    copy(Path(rec['tree']),dst/'models'/n/'checkpoint.tree')
dump(dst/'reference/PARENT_CAMPAIGN_STATE.json',state)
rule={'schema':'CQG_V35_DIRECT_F_EXIT_V1','code':6,'coordinate_order_prefix':['k','r','w'],
      'F_definition':'r-w','whole_box_upper_bound':'r_upper-w_lower',
      'threshold':'alpha.json isolating_interval.lower',
      'alpha_definition_sha256':digest(dst/'alpha.json'),
      'acceptance':'(r_upper-w_lower)*ALPHA_LOW_DEN <= ALPHA_LOW_NUM*UNIT',
      'meaning':'alpha safety, not contradiction; all original-root siblings remain unpaid unless separately certified'}
dump(dst/'DIRECT_F_RULE.json',rule)
(dst/'DIRECT_F_THEOREM.md').write_text('''# CQG Round47: exact direct-height safety exit A6

This extension keeps the V35 original root boxes, every necessary inequality,
physical dictionary, gamma trigger, G definition, low transpose, local wall
certificates, and factor graph unchanged. The two model identities are versioned
with their exact parent model hash and this rule hash. Old accepted partitions
are freshly replayed against the extended semantics before continuation.

For a complete source in an exact box B, the native dictionary gives F=r-w.
Therefore F <= r_upper-w_lower. If that rational upper bound is <= alpha_lower,
then F <= alpha_lower < alpha by the inherited exact alpha isolator. This holds
on every real point of B; it needs no receiver or cofactor sign assumption and
includes r=k. Equality in the rational comparison is safe. Gamma is unchanged.

The leaf certificate is the A6 tag together with its exact ancestral box. With
common positive denominator UNIT, acceptance is the arbitrary-precision integer
comparison (b.hi[1]-b.lo[2])*ALPHA_LOW_DEN <= ALPHA_LOW_NUM*UNIT.
There is no rounded alpha, floating tolerance, or optimization result in this
test. A6 is counted as alpha_safe_leaves and direct_height_leaves, never as a
contradiction. Codes A0 through A5 retain their original meanings.

This rule fills a real logical coverage gap of the earlier A5-only elementary
bound: a valid off-wall source may have r>alpha/2 yet r-w<alpha. It does not
assert that the remaining original roots are fully covered or that all equality
points lie in the four known local neighborhoods. Only full fresh replay of
both roots with zero open leaves can establish complete low-root coverage.
''')
(dst/'build_models.py').write_text('''from pathlib import Path
import json,hashlib
import build_models_original as parent
ROOT=Path(__file__).resolve().parent
def make_model(K,J,typ,branch='low'):
    data=parent.make_model(K,J,typ,branch)
    f=ROOT/'reference/parent_models'/f'{typ}_LOW_ALPHA.json'
    if data!=json.loads(f.read_text()):raise ValueError('Original V35 semantic parent changed')
    rule=json.loads((ROOT/'DIRECT_F_RULE.json').read_text())
    if rule['alpha_definition_sha256']!=hashlib.sha256((ROOT/'alpha.json').read_bytes()).hexdigest():raise ValueError('Rule alpha binding changed')
    data['parent_model_sha256']=hashlib.sha256(f.read_bytes()).hexdigest()
    data['source_version']='V35_CQG_ROUND47_DIRECT_F_2026-09-08'
    data['additional_alpha_rule_sha256']=hashlib.sha256((ROOT/'DIRECT_F_RULE.json').read_bytes()).hexdigest()
    data['legal_safe_terminal_codes']['6']='direct_F_upper<=alpha_lower'
    return data
def headers(data,path):return parent.headers(data,path)
''')
def change(n,old,new):
    p=dst/n;s=p.read_text();assert s.count(old)==1,(n,old,s.count(old));p.write_text(s.replace(old,new))
change('alpha_ports.py',' if code==5:'," if code==6:\n  alpha=json.loads((ROOT/'alpha.json').read_text());a=Q(alpha['isolating_interval']['lower'])\n  return box[1][1]-box[2][0]<=a\n if code==5:")
change('alpha_ports.py',' for i in range(6):',' for i in range(7):')
change('alpha_ports.py'," path=Path(path);cert=data()", " path=Path(path);cert=data()\n rule=json.loads((ROOT/'DIRECT_F_RULE.json').read_text())\n expected="+repr(rule)+"\n if rule!=expected:raise ValueError('Unrecognized direct F theorem definition')\n if model.get('additional_alpha_rule_sha256')!=hashlib.sha256((ROOT/'DIRECT_F_RULE.json').read_bytes()).hexdigest():raise ValueError('Unbound direct F theorem')")
change('alpha_ports.py',' if(code==5)return', ' if(code==6)return Big(b.hi[1]-b.lo[2])*ALPHA_LOW_DEN<=ALPHA_LOW_NUM*UNIT;\n if(code==5)return')
change('alpha_ports.py','for(int c=0;c<6;c++)','for(int c=0;c<7;c++)')
change('source/mc_verify.cpp','std::array<long long,6>safe_counts','std::array<long long,7>safe_counts')
change('source/mc_verify.cpp','code>5','code>6')
change('source/mc_verify.cpp','<<safe_counts[5]<<', '<<safe_counts[5]<<",\\\"direct_height_leaves\\\":"<<safe_counts[6]<<')
change('discovery/frontier_parallel.py','not 0<=int(f[1])<=5','not 0<=int(f[1])<=6')
change('tests/alpha_oracle_probe.cpp','c<6','c<7')
change('verify_alpha_ports.py','range(6)','range(7)')
change('verify_alpha_ports.py',"('unknown_safe_code','A 6\\n')","('unknown_safe_code','A 7\\n')")
change('verify_alpha_ports.py',"'code_comparisons':len(boxes)*6","'code_comparisons':len(boxes)*7")
# Include both adjacent grid points around the exact direct F threshold,
# with r above alpha/2, so an A5 pass cannot mask the new rule's boundary.
change('verify_alpha_ports.py',' for _ in range(48):', ''' # New direct F boundary: F immediately below or above alpha_lower.
 cut_F=(al*unit).__floor__()
 for n in [cut_F-1,cut_F,cut_F+1,cut_F+2]:
  z=list(zero);z[1]=Q(207,100);z[2]=z[1]-Q(n,unit);boxes.append(interval_box(z,0))
 for _ in range(48):''')
# The export must carry the semantic parent and the new theorem definition.
change('export_light.py',"for pattern in ('source/*','theory/*','reference/*.md'):","for pattern in ('source/*','theory/*','reference/*.md','reference/parent_models/*.json'):")
change('export_light.py',"'build_models.py','factor_feasibility.py'", "'build_models.py','build_models_original.py','DIRECT_F_RULE.json','DIRECT_F_THEOREM.md','factor_feasibility.py'")
# Rebuild metadata and generated headers under the new, explicitly bound semantics.
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
newmanifest={'schema':'CQG_V35_DIRECT_F_EXTENSION_STATIC_V1','parent_manifest_sha256':digest(src/'MANIFEST.json'),
             'scope':'V35 original root geometry and necessary rows unchanged; new bound A6 added',
             'files':{str(p.relative_to(dst)):digest(p) for p in sorted(dst.rglob('*')) if p.is_file() and '__pycache__' not in p.parts}}
dump(dst/'MANIFEST.json',newmanifest)
receipt={'status':'SEPARATE_DIRECT_F_RULE_VERSION_BUILT_REPLAY_REQUIRED','working':str(dst),
         'parent_source':str(src),'root_boxes_and_necessary_rows_unchanged':True,
         'parent_models':{n:r['model_sha256'] for n,r in state['models'].items()},
         'new_models':{n:digest(dst/'models'/n/'model.json') for n in state['models']},
         'starting_trees':{n:r['tree_sha256'] for n,r in state['models'].items()},
         'rule_sha256':digest(dst/'DIRECT_F_RULE.json')}
dump(own/'DIRECT_F_EXTENSION_ADOPTION.json',receipt);print(json.dumps(receipt,indent=2))
