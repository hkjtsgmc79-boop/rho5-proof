#!/usr/bin/env python3
"""Cross-check all six exact safe-exit codes; replay an A-leaf at F>gamma.
The A-leaf demonstration has explicit OPEN siblings and is NOT a global tree.
"""
from pathlib import Path
from fractions import Fraction as Q
import subprocess,json,random,tempfile,shutil,sys
from alpha_ports import proves
from local_model import NAMES
from native import verify_matrix
from build_models import make_model,headers
ROOT=Path(__file__).resolve().parent

def run(binary,path,allow=True):
 p=subprocess.run([str(binary),str(path)]+(['--allow-open']if allow else[]),capture_output=True,text=True,timeout=30)
 if p.returncode:raise ValueError(p.stderr)
 return json.loads(p.stdout)

def test(modeldir,exe,work):
 modeldir=Path(modeldir);exe=Path(exe);work=Path(work);data=json.loads((modeldir/'model.json').read_text());headers(data,work)
 for name in ('mc_exact_kernel.hpp',):shutil.copy2(ROOT/'source'/name,work/name)
 shutil.copy2(ROOT/'tests/alpha_oracle_probe.cpp',work/'alpha_oracle_probe.cpp')
 cc=subprocess.run(['g++','-O2','-std=c++17','alpha_oracle_probe.cpp','-o','alpha_probe'],cwd=work,capture_output=True,text=True,timeout=45);assert cc.returncode==0,cc.stderr
 unit=data['root_denominator']*(2**128);cert=json.loads((ROOT/'local_wall_certificate.json').read_text());rad=Q(cert['inner_radius']);boxes=[];rng=random.Random(350091)
 def interval_box(cen,rho):return [(x-rho,x+rho)for x in cen]+[(Q(0),Q(1))]
 for case in cert['cases']:
  cen=list(map(Q,case['center']));boxes += [interval_box(cen,rad),interval_box(cen,rad+Q(1,10**9)),interval_box(cen,Q(0)),interval_box(cen,2*rad)]
  for _ in range(8):
   vec=[x+Q(rng.randint(-140000,140000),10**9)for x in cen];boxes.append(interval_box(vec,Q(rng.randint(0,100),10**9)))
 # Exact weak R0 zero case and an adjacent-minor-only false positive.
 zero=[Q(1),Q(1),Q(-1),Q(0),Q(0),Q(0),Q(0),Q(1),Q(0),Q(0)]+[Q(0)]*12
 boxes.append(interval_box(zero,0));bad=list(zero);bad[9]=Q(1,2);bad[10]=Q(1,10);bad[13]=Q(1,2);bad[15]=Q(1,2);boxes.append(interval_box(bad,0));assert not proves(boxes[-1],4)
 al=Q(json.loads((ROOT/'alpha.json').read_text())['isolating_interval']['lower']);cut=(al*unit/2).__floor__()
 for n in [cut,cut+1]:
  z=list(zero);z[1]=Q(n,unit);boxes.append(interval_box(z,0))
 # New direct F boundary: F immediately below or above alpha_lower.
 cut_F=(al*unit).__floor__()
 for n in [cut_F-1,cut_F,cut_F+1,cut_F+2]:
  z=list(zero);z[1]=Q(207,100);z[2]=z[1]-Q(n,unit);boxes.append(interval_box(z,0))
 # Tube strict boundary, at the boundary and its adjacent integer grid points.
 for case in cert['cases']:
  center=list(map(Q,case['center']));outer=Q(cert['outer_radius'])
  for du in (Q(0),Q(1,100000)):
   for shift in (-1,0,1):
    z=list(center);z[2]+=du;z[7]+=outer-3*du+Q(shift,unit)
    boxes.append(interval_box(z,0))
 for _ in range(48):
  a=[]
  for lo,hi in zip(*data['root_numerators']):
   l=lo+rng.randrange(hi-lo+1);u=l+rng.randrange(hi-l+1);a.append((Q(l,data['root_denominator']),Q(u,data['root_denominator'])))
  boxes.append(a)
 ints=[]
 for box in boxes:
  row=[]
  for a,b in box:
   l=(a*unit).__floor__();h=(b*unit).__ceil__();row.append((l,h))
  ints.append(row)
 payload=str(len(ints))+'\n'+'\n'.join(' '.join(f'{l} {h}'for l,h in row)for row in ints)+'\n'
 ret=subprocess.run([str(work/'alpha_probe')],input=payload,text=True,capture_output=True,timeout=30);assert ret.returncode==0,ret.stderr
 actual=[list(map(int,s.split()))for s in ret.stdout.splitlines()];assert len(actual)==len(boxes)
 for i,box in enumerate(ints):
  rational=[(Q(l,unit),Q(h,unit))for l,h in box];expected=[int(proves(rational,c))for c in range(11)];assert actual[i]==expected,(i,actual[i],expected)
 # An actual F>gamma source belongs to the same II original-root model.
 control=json.loads((ROOT/'strict_offwall_control.json').read_text());ans=verify_matrix(control['matrix']);point=ans['point'];point.append(point[8]*point[10]);assert data['type']=='II'
 products=point+[point[i]*point[j]for i,j in data['pairs']]
 for row in data['rows']:
  assert sum((Q(c)*x for c,x in zip(row['coefficients'],products)),Q(0))<=row['rhs'],row['name']
 root=[[(int(n)<<128)for n in side]for side in data['root_numerators']];lo,hi=root;assert all(Q(l,unit)<=x<=Q(h,unit)for l,x,h in zip(lo,point,hi))
 steps=[]
 while not proves([(Q(l,unit),Q(h,unit))for l,h in zip(lo,hi)],1):
  j=max(range(22),key=lambda i:hi[i]-lo[i]);assert (hi[j]+lo[j])%2==0;m=(hi[j]+lo[j])//2
  if point[j]*unit<=m:steps.append((j,0));hi=list(hi);hi[j]=m
  else:steps.append((j,1));lo=list(lo);lo[j]=m
  assert len(steps)<500
 def envelope(leaf):
  for j,side in reversed(steps):leaf=f'S {j}\n'+(leaf+'O\n'if side==0 else'O\n'+leaf)
  return leaf
 tree=work/'above_gamma_A.tree';tree.write_text(envelope('A 1\n'));proof=run(exe,tree)
 assert proof['alpha_safe_leaves']==1 and proof['local_flow_leaves']==1 and proof['contradiction_leaves']==0 and proof['open']==len(steps)
 rej=[]
 for name,text in [('false_root_A','A 1\n'),('false_weak_R0','A 4\n'),('false_tail_bound','A 5\n'),('unknown_safe_code','A 11\n'),('negative_safe_code','A -1\n'),('wrong_case',envelope('A 2\n')),('truncated',envelope('A 1\n')[:-5]),('unvisited_tail',envelope('A 1\n')+'A 1\n')]:
  f=work/(name+'.tree');f.write_text(text)
  p=subprocess.run([str(exe),str(f),'--allow-open'],capture_output=True,text=True,timeout=10);assert p.returncode!=0,name;rej.append(name)
 p=subprocess.run([str(exe),str(tree)],capture_output=True,text=True,timeout=10);assert p.returncode!=0;rej.append('open_siblings_strict_mode')
 # Structural parser must preserve new A terminal, not turn it into a contradiction.
 sys.path.insert(0,str(ROOT/'discovery'));import frontier_parallel as fp
 assert fp.fields(b'A 1\n')[0]==b'A';ff=fp.collect_frontiers(tree,data,'II_LOW_ALPHA');assert len(ff)==len(steps)
 shutil.copy2(tree,work/'A_PORT_DEMONSTRATION.tree')
 return {'status':'V35_EXACT_ALPHA_EXIT_CODES_AND_ORIGINAL_ROOT_DEMONSTRATION_PASS','boxes_checked':len(boxes),'code_comparisons':len(boxes)*11,'above_gamma_demo':{'F':str(ans['F']),'steps':len(steps),'model_rows_checked':len(data['rows']),'alpha_safe_leaves':proof['alpha_safe_leaves'],'open_siblings':proof['open'],'whole_root_complete':False,'not_weak_R0_or_2r_exit':True},'rejected_bad_trees':rej}

if __name__=='__main__':
 from run_campaign import prepare
 prepare('II_LOW_ALPHA')
 with tempfile.TemporaryDirectory(prefix='v35_alpha_codes_')as t:print(json.dumps(test(ROOT/'models/II_LOW_ALPHA',ROOT/'models/II_LOW_ALPHA/verify',Path(t)),indent=2))
