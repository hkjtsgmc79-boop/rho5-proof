#!/usr/bin/env python3
"""Portable exact H controls: independent fractions, boundaries, bad trees, discovery."""
from pathlib import Path
from fractions import Fraction as Q
import json,sys,subprocess,io,hashlib,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'discovery'))
import frontier_parallel as fp
from run_campaign import prepare
from alpha_ports import proves

def rational_margin(model,lo,hi,weights,t,alpha):
 assert t>0 and len(weights)>0
 native=len(model['variables']);total=native+len(model['pairs']);lo=list(lo);hi=list(hi)
 for i,j in model['pairs']:
  values=[lo[i]*lo[j],lo[i]*hi[j],hi[i]*lo[j],hi[i]*hi[j]]
  lo.append(min(values));hi.append(max(values))
 co=[Q(0)]*total;rhs=Q(0);seen=set()
 for row,w in weights:
  assert w>0 and row not in seen;seen.add(row)
  if row<len(model['rows']):
   d=model['rows'][row]
   for k,a in enumerate(d['coefficients']):co[k]+=w*a
   rhs+=w*d['rhs']
  else:
   n,side=divmod(row-len(model['rows']),4);i,j=model['pairs'][n];y=native+n
   if side==0:ci,cj,cy,b=lo[j],lo[i],-1,lo[i]*lo[j]
   elif side==1:ci,cj,cy,b=hi[j],hi[i],-1,hi[i]*hi[j]
   elif side==2:ci,cj,cy,b=-hi[j],-lo[i],1,-lo[i]*hi[j]
   else:ci,cj,cy,b=-lo[j],-hi[i],1,-hi[i]*lo[j]
   co[i]+=w*ci;co[j]+=w*cj;co[y]+=w*cy;rhs+=w*b
 co[1]-=t;co[2]+=t
 bound=rhs-sum(min(a*l,a*h) for a,l,h in zip(co,lo,hi))
 return bound-t*alpha

def hline(t,weights):
 return ('H '+str(t)+' '+str(len(weights))+' '+' '.join(f'{r} {w}' for r,w in weights)+'\n').encode()

def main():
 start=time.monotonic();out=ROOT/'weighted_height_test_artifacts';out.mkdir(exist_ok=True)
 names=('I_LOW_ALPHA','II_LOW_ALPHA');pins={n:prepare(n) for n in names}
 data={n:json.loads((ROOT/'models'/n/'model.json').read_text()) for n in names}
 alpha=Q(json.loads((ROOT/'alpha.json').read_text())['isolating_interval']['lower'])
 fixtures=json.loads((ROOT/'tests/weighted_height_controls.json').read_text())
 controls=[];negative=[];proposed=[];arithmetic=[]
 for f in fixtures:
  name=f['model'];model=data[name];unit=model['root_denominator']*2**128
  assert f['parent_model_sha256']==model['previous_version_model_sha256']
  lo,hi=fp.root_box(model)
  for dim,side in f['steps']:lo,hi=fp.children(lo,hi,dim)[side]
  assert list(lo)==f['lo'] and list(hi)==f['hi']
  qlo=[Q(v,unit) for v in lo];qhi=[Q(v,unit) for v in hi]
  assert not any(proves(list(zip(qlo,qhi)),i) for i in range(11))
  margin=rational_margin(model,qlo,qhi,f['weights'],f['t'],alpha)
  assert margin<=0 and margin*alpha.denominator*unit**2==int(f['margin'])
  tree=out/(f['id']+'.tree');payload=hline(f['t'],f['weights']);tree.write_bytes(fp.envelope(f['steps'],payload))
  rec=fp.run_verify(ROOT/'models'/name/'verify',tree)
  assert rec['weighted_height_leaves']==1 and rec['alpha_safe_leaves']==1 and rec['contradiction_leaves']==0
  assert rec['open']==len(f['steps'])
  buf=io.BytesIO();fp.copy_focused_payload(tree,f['steps'],buf);assert buf.getvalue()==payload
  strict=subprocess.run([str(ROOT/'models'/name/'verify'),str(tree)],capture_output=True,text=True)
  assert strict.returncode!=0
  controls.append({'id':f['id'],'acceptance':rec,'tree_sha256':fp.digest(tree),'margin_exact':str(margin)})
  arithmetic.append((name,f['id'],lo,hi,f['t'],f['weights'],margin))
  if not f['old_contradiction']:
   d=out/(f['id']+'_discovery');d.mkdir(exist_ok=True);(d/'checkpoint.tree').write_bytes(fp.envelope(f['steps']))
   job={'directory':str(d),'model':name,'model_sha256':pins[name],'steps':f['steps'],
        'focus':fp.key(f['steps']),'rounds':0}
   automatic=fp.job_chunk(job,ROOT,1.0)
   assert automatic['target_open']==0 and automatic['weighted_height_leaves']==1
   assert automatic['contradiction_leaves']==0 and automatic['search_max_solves']==1
   proposed.append({'id':f['id'],'acceptance':automatic})
 f=fixtures[0];name=f['model'];model=data[name];row_count=len(model['rows'])+4*len(model['pairs'])
 weights=f['weights'];t=f['t'];steps=f['steps']
 bad={
  'zero_t':hline(0,weights),'negative_t':hline(-1,weights),'overflow_t':hline(2**63,weights),
  'zero_weight':hline(t,[(weights[0][0],0)]+weights[1:]),
  'negative_weight':hline(t,[(weights[0][0],-1)]+weights[1:]),
  'overflow_weight':hline(t,[(weights[0][0],2**63)]+weights[1:]),
  'duplicate_row':hline(t,[weights[0],weights[0]]),
  'negative_row':hline(t,[(-1,1)]),'row_out_of_range':hline(t,[(row_count,1)]),
  'empty_support':b'H 1 0\n','too_large_support':f'H 1 {row_count+1}\n'.encode(),
  'truncated_weights':b'H 1 1 0\n',
 }
 unit=model['root_denominator']*2**128;qlo=[Q(v,unit) for v in f['lo']];qhi=[Q(v,unit) for v in f['hi']]
 for factor in (2,10,100,1000,10000):
  if t*factor<2**63 and rational_margin(model,qlo,qhi,weights,t*factor,alpha)>0:
   bad['positive_height_margin']=hline(t*factor,weights);break
 assert 'positive_height_margin' in bad
 for label,payload in bad.items():
  p=out/(label+'.tree');p.write_bytes(fp.envelope(steps,payload))
  result=subprocess.run([str(ROOT/'models'/name/'verify'),str(p),'--allow-open'],capture_output=True,text=True)
  assert result.returncode!=0,label
  negative.append(label)
 owned=out/'nonowned_sibling.tree';owned.write_bytes(fp.envelope(steps,hline(t,weights)).replace(b'O\n',b'A 6\n',1))
 try:fp.copy_focused_payload(owned,steps,io.BytesIO())
 except ValueError:negative.append('nonowned_sibling_changed')
 else:raise AssertionError('Owner accepted a changed sibling')
 # Thresholds on adjacent exact grid points; a single r-k<=0 row gives F<=k-w.
 for name,model in data.items():
  unit=model['root_denominator']*2**128;native=len(model['variables']);total=native+len(model['pairs'])
  target=[0]*total;target[0]=-1;target[1]=1
  row=next(i for i,d in enumerate(model['rows']) if d['coefficients']==target and d['rhs']==0)
  floor_alpha=(alpha*unit).__floor__();wf=int(Q(-41325,20000)*unit)
  for shift in (-1,0,1):
   for weight in (1,7,10**12):
    lo,hi=map(list,fp.root_box(model));lo[0]=hi[0]=floor_alpha+shift+wf;lo[2]=hi[2]=wf
    w=[(row,weight)];m=rational_margin(model,[Q(x,unit) for x in lo],[Q(x,unit) for x in hi],w,weight,alpha)
    assert (m<=0)==(shift<=0)
    arithmetic.append((name,f'boundary_{shift}_{weight}',lo,hi,weight,w,m))
 probe=out/'margin_probe.cpp';probe.write_text('''#include "weighted_height.hpp"
#include <iostream>
#include <string>
int main(){try{std::string id;while(std::cin>>id){EBox b;for(auto&v:b.lo)std::cin>>v;for(auto&v:b.hi)std::cin>>v;long long t;int n;std::cin>>t>>n;std::vector<std::pair<int,long long>>w;for(int k=0;k<n;k++){int r;long long v;std::cin>>r>>v;w.push_back({r,v});}if(!std::cin)throw std::runtime_error("truncated");std::cout<<id<<' '<<weighted_height_margin(b,w,t)<<'\\n';}}catch(const std::exception&e){std::cerr<<e.what();return 1;}}
''')
 for name in names:
  exe=out/('margin_probe_'+name)
  p=subprocess.run(['g++','-O2','-std=c++17','-I',str(ROOT/'models'/name/'build'),str(probe),'-o',str(exe)],text=True,capture_output=True)
  assert p.returncode==0,p.stderr
  chosen=[x for x in arithmetic if x[0]==name];unit=data[name]['root_denominator']*2**128
  lines=[' '.join([label]+list(map(str,lo))+list(map(str,hi))+[str(t),str(len(w))]+[str(v) for pair in w for v in pair]) for _,label,lo,hi,t,w,m in chosen]
  p=subprocess.run([str(exe)],input='\n'.join(lines)+'\n',capture_output=True,text=True);assert p.returncode==0,p.stderr
  got={s.split()[0]:int(s.split()[1]) for s in p.stdout.splitlines()}
  for _,label,lo,hi,t,w,m in chosen:assert got[label]==m*alpha.denominator*unit**2,label
 answer={'status':'WEIGHTED_HEIGHT_EXACT_CONTROLS_PASSED','models':pins,'real_original_root_controls':controls,
  'automatic_discovery_controls':proposed,'arithmetic_comparisons':len(arithmetic),'rejected_bad_controls':negative,
  'source_rule_sha256':fp.digest(ROOT/'WEIGHTED_HEIGHT_RULE.json'),'whole_root_credit':False,'seconds':time.monotonic()-start}
 (out/'RESULT.json').write_text(json.dumps(answer,indent=2)+'\n')
 print(json.dumps({k:v for k,v in answer.items() if k not in ('real_original_root_controls','automatic_discovery_controls')},indent=2))
if __name__=='__main__':main()
