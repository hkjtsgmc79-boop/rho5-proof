from pathlib import Path
from fractions import Fraction as Q
import json,sys,random,subprocess,shutil,time,importlib.util
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from physical_packets import build_packets,solve_box
from factor_feasibility import Interval,check_witness,verify
ROOT=Path(__file__).resolve().parents[1];UNIT=(10**9)<<128

def compile_probe(typ):
 b=ROOT/('build_probe_'+typ);b.mkdir(exist_ok=True)
 for n in ('mc_exact_kernel.hpp','rankone_oracle.hpp','factor_graph.hpp','factor_oracle.hpp','factor_probe.cpp'):shutil.copy2(ROOT/'source'/n,b/n)
 shutil.copy2(ROOT/'models'/(typ+'209_210_low')/'mc_exact_model.hpp',b/'mc_exact_model.hpp')
 subprocess.run(['g++','-O2','-std=c++17','factor_probe.cpp','-o','probe'],cwd=b,check=True)
 return b/'probe'

def sample_tree(d):
 data=json.loads((d/'model.json').read_text());rr=data['root_numerators'];out=[];opens=[];rng=random.Random(340+
 sum(map(ord,d.name)));count=0
 def visit(f,lo,hi,depth,path):
  nonlocal count
  z=f.readline().split();tag=z[0]
  if tag=='S':
   j=int(z[1]);m=(lo[j]+hi[j])//2;lh=hi[:];lh[j]=m;hl=lo[:];hl[j]=m
   visit(f,lo,lh,depth+1,path+'0');visit(f,hl,hi,depth+1,path+'1')
  elif tag=='C':
   count+=1;record={'lo':lo,'hi':hi,'depth':depth,'path':path,'old':'C','model':d.name}
   if len(out)<32:out.append(record)
   else:
    n=rng.randrange(count)
    if n<32:out[n]=record
  elif tag=='O':opens.append({'lo':lo,'hi':hi,'depth':depth,'path':path,'old':'O','model':d.name})
 with(d/'checkpoint.tree').open()as f:visit(f,[n<<128 for n in rr[0]],[n<<128 for n in rr[1]],0,'')
 return out+opens

stats={};saved=[]
for typ in ('I','II'):
 exe=compile_probe(typ)
 cases=[c for c in json.loads((ROOT/'evidence/physical_oracle_probe_boxes.json').read_text()) if c['model'].startswith(typ+'2')]
 txt=''.join('B '+' '.join(str(z)for pair in zip(c['lo'],c['hi'])for z in pair)+'\n'for c in cases)
 t=time.time();p=subprocess.run([str(exe),'box'],input=txt,text=True,capture_output=True,check=True)
 vals=[x.split()for x in p.stdout.splitlines()];assert len(vals)==len(cases)
 new=0;detailed=[]
 for j,(c,val)in enumerate(zip(cases,vals)):
  old,n=int(val[0]),int(val[1]);c.update(old_oracle=old,new_oracle=n,seconds=float(val[2]))
  if old<0 and n>=0:new+=1;detailed.append(c)
  if j<6 or (c['old']=='O' and j%3==0):
   bounds=[(Q(l,UNIT),Q(h,UNIT))for l,h in zip(c['lo'],c['hi'])];res=solve_box(bounds,typ)
   code=res.get('layer',-1);assert code==n,(typ,j,n,code)
   if code>=0 and code!=3:
    pk=res['packet'];verify([Interval(*z)for z in pk['left']],[Interval(*z)for z in pk['right']],[[Interval(*z)for z in row]for row in pk['cells']],res['certificate'])
  saved.append(c)
 stats[typ]={'boxes':len(cases),'additional_exclusions_beyond_old_tail_oracle':new,'seconds':time.time()-t,'new_rule_codes':{str(t):sum(int(v[1])==t for v in vals)for t in (-1,0,1,2,3)}}
# frozen probe data are read-only
# result is emitted below
# Existing complete matrices are controls only; never require their height >= target.
spec=importlib.util.spec_from_file_location('native',ROOT/'reference/v33_native_checker.py');nm=importlib.util.module_from_spec(spec);spec.loader.exec_module(nm)
fixtures=json.loads((ROOT/'reference/v33_regression_matrices.json').read_text());control=0
for name,M in fixtures.items():
 src=nm.native(M);nm.blocks(M);D=src['D'];H=nm.residual(src)
 # Oracle uses symmetric X H. Proper B controls deliberately not forced into X.
 if not(H[0][0]==H[0][1]==H[1][0]):continue
 vals=[src['k'],H[0][0],H[1][1],D[0][1],D[0][2],D[1][0]/src['k'],D[2][0]/src['k'],src['p'],src['e'],src['beta']]+src['u']+src['x']+src['v']+src['q']
 for typ in ('I','II'):
  value=src['e']*(src['beta']if typ=='I'else src['u'][0]);vec=vals+[value]
  bounds=[(Q((x*10**9).__floor__(),10**9)-Q(1,10**9),Q((x*10**9).__ceil__(),10**9)+Q(1,10**9))for x in vec]
  packets,error=build_packets(bounds,typ);assert error is None,(name,typ,error)
  witnesses=[([Q(1)]+src['x'],[src['p']]+src['q']),([src['beta']]+src['u'],[src['e']]+src['v']),([vals[5],vals[6]],[vals[0],vals[3],vals[4]])]
  for pk,(a,b)in zip(packets,witnesses):assert check_witness([Interval(*z)for z in pk['left']],[Interval(*z)for z in pk['right']],[[Interval(*z)for z in row]for row in pk['cells']],a,b),(name,typ,pk['name'])
  assert solve_box(bounds,typ)['status']=='NOT_EXCLUDED';control+=1
print(json.dumps({'status':'PHYSICAL_INTERVAL_ORACLE_DIFFERENTIAL_PASS','statistics':stats,'actual_X_controls':control}))
