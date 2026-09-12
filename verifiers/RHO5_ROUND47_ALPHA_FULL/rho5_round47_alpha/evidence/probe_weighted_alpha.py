#!/usr/bin/env python3
"""Bounded independent diagnostic, no changes to the active campaign or rules."""
from pathlib import Path
import json,subprocess,os,time,hashlib
own=Path('/root/microscope_ws/rho5_cqg_v35_low_alpha_20260908/attempt_01')
root=own/'working_flow_tube';out=own/'weighted_alpha_probe';out.mkdir(exist_ok=True)
manifest_path=root/'campaign_low_alpha/wave_0004/FRONTIER_MANIFEST.json'
m=json.loads(manifest_path.read_text())
pool=[j for j in m['jobs'] if j['model']=='II_LOW_ALPHA' and not j.get('alpha_priority')]
pool.sort(key=lambda j:(len(j['steps']),j['id']))
sample=[pool[i*(len(pool)-1)//95] for i in range(96)]
(out/'SAMPLES.json').write_text(json.dumps({'manifest_sha256':hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
  'model_sha256':sample[0]['model_sha256'],'jobs':sample},indent=2)+'\n')
(out/'boxes.txt').write_text('\n'.join(' '.join([j['id'],str(len(j['steps']))]+list(map(str,j['lo']))+list(map(str,j['hi']))) for j in sample)+'\n')
source=(root/'discovery/discover_hybrid.cpp').read_text().split('Found solve_box_precise(')[0]
source=source.replace('struct Found{bool closed=false;Weights w;std::vector<double> val;};',
  'struct Found{bool closed=false;Weights w;std::vector<double> val;long long height_t=0;Big height_margin=0;double height_lp=0;};')
helper=r'''
Big weighted_height_margin(const EBox&b,const Weights&weights,long long t){
 if(t<=0||weights.empty()||weights.size()>EB+4*epairs.size())throw std::runtime_error("bad height certificate");
 std::array<Big,EN>co{},lo,hi;Big rhs=0;std::vector<bool>seen(EB+4*epairs.size(),false);
 for(auto[row,w]:weights){if(row<0||row>=(int)seen.size()||seen[row])throw std::runtime_error("bad row");seen[row]=true;add_exact_row(b,row,Big(w),co,rhs);}
 co[1]-=Big(t)*UNIT;co[2]+=Big(t)*UNIT;
 product_bounds(b,lo,hi);
 for(int j=0;j<EN;j++)rhs-=co[j]*(co[j]>=0?lo[j]:hi[j]);
 return rhs*ALPHA_LOW_DEN-Big(t)*ALPHA_LOW_NUM*UNIT2;
}
'''
source=source.replace('const double US=',helper+'\nconst double US=')
insert=r'''
 out.height_lp=ans+lo[1]-lo[2];
 if(std::isfinite(ans)&&x.size()==NX){
  auto ww=lp.dual();double mx=1;std::vector<double>raw(scales.size());
  for(size_t i=0;i<raw.size();i++){raw[i]=std::max(0.,ww[i])/scales[i];mx=std::max(mx,raw[i]);}
  if(std::isfinite(mx))for(double prec:{1e6,1e9,1e12,1e15,1e18}){
   if(prec/mx<1)continue;long long t=std::llround(prec/mx);Weights w;
   for(size_t i=0;i<raw.size();i++)if(raw[i]>0){long long wi=std::llround(t*raw[i]);if(wi>0)w.push_back({i,wi});}
   if(!w.empty()){Big margin=weighted_height_margin(nd,w,t);if(margin<=0){out.height_t=t;out.height_margin=margin;out.w=w;break;}}
  }
 }
'''
needle='bool valid=std::isfinite(ans)&&x.size()==NX;'
assert source.count(needle)==1
source=source.replace(needle,insert+'\n '+needle)
# The diagnostic does not need contradiction proposals to overwrite the height witness.
source=source.replace('out.closed=true;out.w=std::move(w);break;','out.closed=true;if(!out.height_t)out.w=std::move(w);break;')
source+=r'''
int main(int argc,char**argv){try{
 std::ifstream input(argv[1]);std::string id;int depth;
 while(input>>id>>depth){EBox b;b.depth=depth;for(auto&v:b.lo)input>>v;for(auto&v:b.hi)input>>v;if(!input)throw std::runtime_error("truncated box");
  int old=alpha_exit(b);Found f=solve_box_fast(b);
  std::cout<<"{\"id\":\""<<id<<"\",\"depth\":"<<depth<<",\"old_alpha_code\":"<<old
   <<",\"closed_contradiction\":"<<(f.closed?"true":"false")<<",\"lp_height_approx\":";
  if(std::isfinite(f.height_lp))std::cout<<std::setprecision(17)<<f.height_lp;else std::cout<<"null";
  std::cout<<",\"height_t\":"<<f.height_t<<",\"margin\":\""<<f.height_margin<<"\",\"weights\":[";
  for(size_t i=0;i<f.w.size();i++){if(i)std::cout<<',';std::cout<<'['<<f.w[i].first<<','<<f.w[i].second<<']';}
  std::cout<<"]}"<<std::endl;
 }
}catch(const std::exception&e){std::cerr<<e.what()<<std::endl;return 1;}}
'''
(out/'probe.cpp').write_text(source)
env=os.environ.copy();env.update(OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1',
  TMPDIR=str(own/'tmp'),CPLUS_INCLUDE_PATH='/root/microscope_ws/controller_v31_review_20260907.cRz00v/deps/usr/include')
t=time.monotonic()
p=subprocess.run(['g++','-O3','-std=c++17','-I',str(root/'models/II_LOW_ALPHA/build'),str(out/'probe.cpp'),'-o',str(out/'probe')],env=env,text=True,capture_output=True)
(out/'COMPILE.log').write_text(p.stdout+p.stderr);p.check_returncode()
with (out/'RESULTS.jsonl').open('w') as f:
 p=subprocess.run([str(out/'probe'),str(out/'boxes.txt')],env=env,stdout=f,stderr=subprocess.PIPE,text=True,timeout=240)
(out/'STDERR.log').write_text(p.stderr);p.check_returncode()
records=[json.loads(s) for s in (out/'RESULTS.jsonl').read_text().splitlines()]
answer={'status':'EXACT_WEIGHTED_ALPHA_DIAGNOSTIC_NO_ORIGINAL_ROOT_CREDIT','sample_size':len(records),
 'existing_alpha':sum(r['old_alpha_code']>=0 for r in records),'contradiction':sum(r['closed_contradiction'] for r in records),
 'weighted_alpha':sum(r['height_t']>0 for r in records),
 'new_weighted_alpha':sum(r['height_t']>0 and r['old_alpha_code']<0 and not r['closed_contradiction'] for r in records),
 'seconds_including_compile':time.monotonic()-t,
 'model_sha256':sample[0]['model_sha256'],'all_original_frontiers_preserved':True}
(own/'WEIGHTED_ALPHA_PROBE.json').write_text(json.dumps(answer,indent=2)+'\n');print(json.dumps(answer,indent=2))
