#!/usr/bin/env python3
"""Stage a conservative exact height-certificate extension, without tree adoption."""
from pathlib import Path
import json,hashlib,shutil,subprocess,sys
own=Path('/root/microscope_ws/rho5_cqg_v35_low_alpha_20260908/attempt_01')
src=own/'working_flow_tube';dst=own/'working_weighted_height'
assert not dst.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
def change(n,old,new,count=1):
 p=dst/n;s=p.read_text();assert s.count(old)==count,(n,old,s.count(old));p.write_text(s.replace(old,new))
manifest=json.loads((src/'MANIFEST.json').read_text())
for n,h in manifest['files'].items():
 assert sha(src/n)==h,n
 # Final accepted trees will be adopted only after the active wave stops.
 if Path(n).name not in ('checkpoint.tree','checkpoint.tree.gz'):copy(src/n,dst/n)
copy(src/'MANIFEST.json',dst/'reference/FLOW_TUBE_PARENT_MANIFEST.json')
parents={}
for n in ('I_LOW_ALPHA','II_LOW_ALPHA'):
 p=src/'models'/n/'model.json';parents[n]=sha(p)
 copy(p,dst/'reference/flow_tube_parent_models'/f'{n}.json')
rule={'schema':'rho5.exact.weighted-height.v1','terminal':'H t n row_1 w_1 ... row_n w_n',
 'objective':'F=r-w','alpha_definition_sha256':sha(dst/'alpha.json'),
 'weights':'distinct original physical/McCormick row indices; positive signed-64-bit integer weights',
 't':'positive signed-64-bit integer','acceptance':'B-min_box((sum(weights*rows)-t*F)) <= t*alpha_lower',
 'box':'the original exact ancestral box, with outward corner bounds for each lifted product',
 'scope':'every original physical source in that box; gamma remains a localization trigger',
 'arithmetic':'all final acceptance uses unbounded integers; numerical duals are proposals only',
 'classification':'alpha safety, never a contradiction; original C/R/P and A0..10 unchanged'}
dump(dst/'WEIGHTED_HEIGHT_RULE.json',rule)
(dst/'WEIGHTED_HEIGHT_THEOREM.md').write_text('''# Exact weighted height certificates

Let u contain the native coordinates and the true lifted pair products of an
original physical source in an original ancestral box. The unchanged model
and the box McCormick inequalities imply a_j.u <= b_j. Let w_j be positive
integers on distinct allowed rows, t a positive integer, a=sum(w_j*a_j),
B=sum(w_j*b_j), and h.u=F=r-w. Put c=a-t*h. If each lifted coordinate lies in
[L_i,U_i], then m=sum_i min(c_i*L_i,c_i*U_i) <= c.u. Therefore

    t*F = a.u-c.u <= B-m.

The exact condition B-m <= t*alpha_lower proves F <= alpha_lower < alpha.
No assumption that the numerical LP solution or dual is correct is needed.
Arbitrary positive integer candidates are safe only after this comparison.
Correlations discarded in taking product intervals merely weaken the bound.
This proof applies to the full original root, including r=k and the actual G,
subject to the unchanged necessary rows. It adds no sign, rank, contact, or
gamma upper-bound assumption. It does not enlarge any local flow certificate.

The integer kernel uses UNIT=root_denominator*2^128. Native coordinates have
denominator UNIT; lifted products and row right sides have denominator UNIT^2.
After adding the existing exact rows, subtract t*UNIT from the r coefficient
and add t*UNIT to the w coefficient. Subtract the interval lower bound of the
remaining linear form from the weighted right side. Accept exactly when this
integer times alpha_lower.denominator is at most
t*alpha_lower.numerator*UNIT^2. This is the displayed inequality with no
rounding. The alpha definition and isolator are rebuilt and verified as before.

Syntax is `H t n row_1 w_1 ... row_n w_n`. Support is nonempty and bounded by
the number of allowed rows; duplicate/out-of-range rows, nonpositive weights,
nonpositive t, integer overflow on input, malformed or truncated data are
rejected. H leaves contribute to alpha_safe_leaves and weighted_height_leaves,
not contradiction_leaves. The old A0..10 and C/R/P conditions are unchanged.
No original-root credit is added by staging this source or testing controls.
Both complete original roots still require strict independent cold replay.
''')
copy(dst/'build_models.py',dst/'build_models_flow_parent.py')
(dst/'build_models.py').write_text('''from pathlib import Path
import json,hashlib
import build_models_flow_parent as parent
ROOT=Path(__file__).resolve().parent
EXPECTED_RULE='''+repr(rule)+'''
def make_model(K,J,typ,branch='low'):
 data=parent.make_model(K,J,typ,branch)
 p=ROOT/'reference/flow_tube_parent_models'/f'{typ}_LOW_ALPHA.json'
 if data!=json.loads(p.read_text()):raise ValueError('Flow-tube semantic parent changed')
 rule=json.loads((ROOT/'WEIGHTED_HEIGHT_RULE.json').read_text())
 if rule!=EXPECTED_RULE:raise ValueError('Weighted height rule changed')
 if rule['alpha_definition_sha256']!=hashlib.sha256((ROOT/'alpha.json').read_bytes()).hexdigest():raise ValueError('Weighted height alpha binding changed')
 data['source_version']='V35_CQG_ROUND47_WEIGHTED_HEIGHT_2026-09-08'
 data['previous_version_model_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
 data['weighted_height_rule_sha256']=hashlib.sha256((ROOT/'WEIGHTED_HEIGHT_RULE.json').read_bytes()).hexdigest()
 data['legal_safe_terminal_codes']['H']='exact_positive_weighted_height_upper_bound'
 return data
def headers(data,path):return parent.headers(data,path)
''')
(dst/'source/weighted_height.hpp').write_text('''#pragma once
#include "mc_exact_kernel.hpp"
#include "alpha_ports.hpp"
// Exact positive row combinations certify an upper bound for F=r-w.
inline Big weighted_height_margin(const EBox&b,const std::vector<std::pair<int,long long>>&weights,long long t){
 if(t<=0||weights.empty()||weights.size()>EB+4*epairs.size())throw std::runtime_error("bad height certificate");
 std::array<Big,EN>co{},lo,hi;Big rhs=0;std::vector<bool>seen(EB+4*epairs.size(),false);
 for(auto[row,w]:weights){
  if(row<0||row>=(int)seen.size()||seen[row])throw std::runtime_error("invalid/duplicate height row");
  seen[row]=true;add_exact_row(b,row,Big(w),co,rhs);
 }
 co[1]-=Big(t)*UNIT;co[2]+=Big(t)*UNIT;
 product_bounds(b,lo,hi);
 for(int j=0;j<EN;j++)rhs-=co[j]*(co[j]>=0?lo[j]:hi[j]);
 return rhs*ALPHA_LOW_DEN-Big(t)*ALPHA_LOW_NUM*UNIT2;
}
''')
for p in ('run_campaign.py','verify_task.py','verify_all.py'):
 change(p,"'mc_exact_kernel.hpp','rankone_oracle.hpp'","'mc_exact_kernel.hpp','weighted_height.hpp','rankone_oracle.hpp'")
for p in ('source/mc_verify.cpp','discovery/discover_hybrid.cpp'):
 change(p,'#include "alpha_ports.hpp"','#include "alpha_ports.hpp"\n#include "weighted_height.hpp"')
change('source/mc_verify.cpp','long long safe_leaves=0;','long long safe_leaves=0;long long weighted_safe_leaves=0;')
change('source/mc_verify.cpp',' }else if(tag=="R"){',''' }else if(tag=="H"){
  long long objective_weight;int n;
  if(!(in>>objective_weight>>n)||objective_weight<=0||n<1||n>EB+4*(int)epairs.size())throw std::runtime_error("bad height support count/objective weight");
  std::vector<std::pair<int,long long>>weights;
  for(int i=0;i<n;i++){int row;long long w;if(!(in>>row>>w))throw std::runtime_error("truncated/out-of-range height weight");weights.emplace_back(row,w);}
  if(weighted_height_margin(box,weights,objective_weight)>0)throw std::runtime_error("height leaf does NOT bound F by alpha");
  leaves++;safe_leaves++;weighted_safe_leaves++;total_support+=n;maxsupport=std::max(maxsupport,n);
 }else if(tag=="R"){''')
change('source/mc_verify.cpp','<<safe_leaves<<','<<safe_leaves<<",\\\"weighted_height_leaves\\\":"<<weighted_safe_leaves<<')
change('discovery/frontier_parallel.py',"    elif tag in (b'R',b'P'):","""    elif tag==b'H':
        if len(f)<3 or int(f[1])<=0 or int(f[2])<1 or len(f)!=3+2*int(f[2]):raise ValueError('Malformed weighted height leaf')
    elif tag in (b'R',b'P'):""")
change('export_light.py',"'reference/direct_f_parent_models/*.json'","'reference/direct_f_parent_models/*.json','reference/flow_tube_parent_models/*.json'")
change('export_light.py',"'build_models_original.py'","'build_models_original.py','build_models_flow_parent.py'")
change('export_light.py',"'DIRECT_F_RULE.json'","'DIRECT_F_RULE.json','WEIGHTED_HEIGHT_RULE.json','WEIGHTED_HEIGHT_THEOREM.md'")
change('discovery/discover_hybrid.cpp','struct Found{bool closed=false;Weights w;std::vector<double> val;};',
 'struct Found{bool closed=false;Weights w;std::vector<double> val;long long height_t=0;Weights height_weights;};')
proposal='''// Floating dual coefficients propose a witness; only the integer margin accepts it.
 if(std::isfinite(ans)&&x.size()==NX){
  auto ww=lp.dual();double mx=1;std::vector<double>raw(scales.size());
  for(size_t i=0;i<raw.size();i++){raw[i]=std::max(0.,ww[i])/scales[i];mx=std::max(mx,raw[i]);}
  if(std::isfinite(mx))for(double prec:{1e6,1e9,1e12,1e15,1e18}){
   if(prec/mx<1)continue;long long t=std::llround(prec/mx);Weights w;
   for(size_t i=0;i<raw.size();i++)if(raw[i]>0){long long wi=std::llround(t*raw[i]);if(wi>0)w.push_back({i,wi});}
   if(!w.empty()&&weighted_height_margin(nd,w,t)<=0){out.height_t=t;out.height_weights=std::move(w);break;}
  }
 }
 '''
change('discovery/discover_hybrid.cpp','bool valid=std::isfinite(ans)&&x.size()==NX;',proposal+'bool valid=std::isfinite(ans)&&x.size()==NX;',2)
change('discovery/discover_hybrid.cpp','if(first.closed||first.val.size()==NX)return first;',
       'if(first.closed||first.height_t>0||first.val.size()==NX)return first;')
change('discovery/discover_hybrid.cpp','void refine(const EBox&box,std::ostream&out){','''void emit_height(std::ostream&out,const Found&f){
 out<<"H "<<f.height_t<<' '<<f.height_weights.size();
 for(auto[row,w]:f.height_weights)out<<' '<<row<<' '<<w;
 out<<'\\n';leaves++;
}
void refine(const EBox&box,std::ostream&out){''')
change('discovery/discover_hybrid.cpp','if(f.closed){emit_leaf(out,f.w);return;}',
       'if(f.closed){emit_leaf(out,f.w);return;}\n if(f.height_t>0){emit_height(out,f);return;}')
change('discovery/discover_hybrid.cpp',' }else if(op=="R"){',''' }else if(op=="H"){
 long long t;int n;if(!(in>>t>>n)||t<=0||n<1||n>EB+4*(int)pairs.size())throw std::runtime_error("bad old height leaf");
 Weights w;for(int i=0;i<n;i++){int row;long long v;if(!(in>>row>>v))throw std::runtime_error("truncated old height weight");w.push_back({row,v});}
 if(weighted_height_margin(box,w,t)>0)throw std::runtime_error("invalid old height certificate");
 out<<"H "<<t<<' '<<n;for(auto[row,v]:w)out<<' '<<row<<' '<<v;out<<'\\n';old_leaves++;
 }else if(op=="R"){''')
samples={j['id']:j for j in json.loads((own/'weighted_alpha_probe/SAMPLES.json').read_text())['jobs']}
records=[json.loads(s) for s in (own/'weighted_alpha_probe/RESULTS.jsonl').read_text().splitlines()]
fixtures=[]
for row in records:
 if row['height_t']<=0:continue
 j=samples[row['id']]
 fixtures.append({'id':row['id'],'model':j['model'],'parent_model_sha256':j['model_sha256'],
                  'steps':j['steps'],'lo':j['lo'],'hi':j['hi'],'t':row['height_t'],
                  'weights':row['weights'],'margin':row['margin'],'old_alpha_code':row['old_alpha_code'],
                  'old_contradiction':row['closed_contradiction']})
dump(dst/'tests/weighted_height_controls.json',fixtures)
program='''from pathlib import Path
import json
from build_models import make_model,headers
root=Path.cwd()
for name in ('I_LOW_ALPHA','II_LOW_ALPHA'):
 p=root/'models'/name;old=json.loads((p/'model.json').read_text())
 new=make_model(old['K'],old['J'],old['type'],old['branch'])
 for k in ('variables','root_numerators','root_denominator','rows','pairs','K','J','type','branch','target','alpha_definition_sha256','alpha_ports_certificate_sha256'):
  assert old[k]==new[k],k
 headers(new,p);(p/'model.json').write_text(json.dumps(new,indent=2)+'\\n')
'''
r=subprocess.run([sys.executable,'-c',program],cwd=dst,text=True,capture_output=True)
assert r.returncode==0,r.stdout+r.stderr
dump(dst/'MANIFEST.json',{'schema':'CQG_V35_WEIGHTED_HEIGHT_STATIC_V1','scope':'same complete original roots with exact H alpha-safety certificates; no trees adopted yet',
 'files':{str(p.relative_to(dst)):sha(p) for p in sorted(dst.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and p!=dst/'MANIFEST.json'}})
result={'status':'WEIGHTED_HEIGHT_SOURCE_STAGED_NO_ROOT_CREDIT','working':str(dst),'parent_source':str(src),
 'parent_models':parents,'new_models':{n:sha(dst/'models'/n/'model.json') for n in parents},
 'rule_sha256':sha(dst/'WEIGHTED_HEIGHT_RULE.json'),'original_roots_and_rows_unchanged':True,
 'factor_graph_sha256':sha(dst/'source/factor_graph.hpp'),'tests_and_original_root_adoption_pending':True}
dump(own/'WEIGHTED_HEIGHT_STAGE.json',result);print(json.dumps(result,indent=2))
