#!/usr/bin/env python3
"""Rebuild frozen polynomials/roots, audit CHSH signs and rational controls.
This is source/dictionary validation, not a whole-domain exclusion by itself.
"""
from pathlib import Path
from fractions import Fraction as Q
import json
import sympy as S
from build_model import make_model
from make_contact_case import add_case
from native_checker import native,build,blocks,residual
ROOT=Path(__file__).resolve().parent

def conjugate(M,signs):return [[M[i][j]*signs[i]*signs[j] for j in range(5)] for i in range(5)]
def normalize(M,transpose=False,fold=True):
 M=[[Q(t) for t in row] for row in M]
 if transpose:M=conjugate([list(r) for r in zip(*M)],[1,-1,1,1,1])
 ss=native(M)
 if ss['e']<0:M=conjugate(M,[1,-1,1,1,1])
 ss=native(M)
 if ss['x'][0]<0:M=conjugate(M,[1,1,-1,-1,-1])
 ss=native(M)
 if ss['D'][0][1]>0:M=conjugate(M,[1,1,1,-1,-1])
 ss=native(M);b=ss['p']*ss['x'][0];h=-ss['q'][0]
 typ='I' if b>=1 and h>=1 else ('II' if b>=1 and h<=1 else 'III')
 if typ=='III':return normalize(M,True,fold)
 if typ=='I' and fold and ss['u'][0]<ss['v'][0]:return normalize(M,True,False)
 return ss,typ

def values(s):
 D=s['D'];k=D[0][0];H=residual(s)
 assert H[0][0]==H[0][1]==H[1][0]>0
 return [k,H[0][0],H[1][1],D[0][1],D[0][2],D[1][0]/k,D[2][0]/k,s['p'],s['e'],s['beta']]+s['u']+s['x']+s['v']+s['q']

def eval_poly(row,data,xx):
 yy=xx+[xx[i]*xx[j] for i,j in data['pairs']]
 # Every exported row is a positive scalar multiple of a necessary slack.
 return Q(row['rhs'])-sum(Q(c)*x for c,x in zip(row['coefficients'],yy))

def main():
 audited=[]
 for path in sorted((ROOT/'models').glob('*/model.json')):
  data=json.loads(path.read_text())
  if 'contact_cases' in data or 'subdomain' in data:continue
  rebuilt=make_model(data['K'],data['J'],data['type'],data['extra_anchor'],data.get('norm_coupling',False))
  if 'contact_case' in data:rebuilt=add_case(rebuilt,int(data['contact_case']['id']))
  for key in ['variables','target','root_denominator','root_numerators','pairs','rows']:assert data[key]==rebuilt[key],(path,key)
  assert all(z['positive_scale'] and Q(z['positive_scale'])>0 for z in data['rows'])
  assert len(data['variables'])==23
  audited.append({'model':path.parent.name,'rows':len(data['rows']),'products':len(data['pairs'])})
 # Independent CHSH sum-of-nonnegative-products identity.
 a,b,z,t,h=S.symbols('a b z t h')
 right=(1-a)*(h+z)*(h+t)+(1-b)*(h+z)*(h-t)+(1+b)*(h-z)*(h+t)+(1+a)*(h-z)*(h-t)
 assert S.expand(2*h*(2*h-a*z-a*t-b*z+b*t)-right)==0
 E,H,G,T,g,sg=S.symbols('E H G T g sg')
 for sign in (-1,1):
  for branch in ('sum','diff'):
   lhs=1-g+G+(g*T if branch=='sum' else -g*T)+sign*(E+H if branch=='sum' else E-H)
   rhs=(1+sign*E)*(1+sign*H)+(G-g)*(1-T) if branch=='sum' else (1+sign*E)*(1-sign*H)+(G-g)*(1+T)
   assert S.rem(S.Poly(S.expand(rhs-lhs),E,H,G,T,g),S.Poly(E*H-G*T,E,H,G,T,g))==0
 # Two exact type controls at k=2.1; height is deliberately low, not a root test.
 sources=[]
 for typ,p,e,be,u0,v0,x0,q0 in [('I',Q(3,2),Q(1),Q(1),Q(1,2),Q(1,2),Q(1),Q(-3,2)),('II',Q(3,2),Q(1),Q(7,10),Q(1),Q(-1,2),Q(1),Q(-3,5))]:
  ss=dict(p=p,e=e,beta=be,u=[u0,Q(0),Q(0)],x=[x0,Q(0),Q(0)],v=[v0,Q(0),Q(0)],q=[q0,Q(0),Q(0)],D=[[Q(21,10),0,0],[0,Q(1),Q(1)],[0,Q(1),Q(-1)]],k=Q(21,10))
  M=build(ss);blocks(M);ss2,typ2=normalize(M);assert typ2==typ;sources.append((typ+'_control',ss2,typ2,'21/10'))
  if typ=='II':
   tr=conjugate([list(r) for r in zip(*M)],[1,-1,1,1,1]);ss3,ty3=normalize(tr);assert ty3=='II';blocks(build(ss3));sources.append(('III_to_II_control',ss3,ty3,'21/10'))
 # The handoff witness is below both gamma and k=2.1, so use K=2.05 only.
 W=json.loads((ROOT/'witness.json').read_text())['parameters'];f=lambda n:Q(W[n]);kk,AA,BB,cc,dd,rr,ww=[f(n) for n in ['k','A','B','c','d','r','w']]
 ss=dict(p=f('p'),e=f('e'),beta=f('beta'),u=list(map(Q,W['u'])),x=list(map(Q,W['x'])),v=list(map(Q,W['vv'])),q=list(map(Q,W['qq'])),D=[[kk,AA,BB],[cc*kk,rr+cc*AA,rr+cc*BB],[dd*kk,rr+dd*AA,ww+dd*BB]],k=kk)
 for tr in (False,True):
  z,ty=normalize(build(ss),tr);blocks(build(z));sources.append(('nearpeak'+str(tr),z,ty,'41/20'))
 rowchecks=0;rec=[]
 for name,z,typ,K in sources:
  for extra in (False,True):
   data=make_model(K,'43/20',typ,True,extra)
   xx=values(z);xx.append(z['e']*(z['beta'] if typ=='I' else z['u'][0]))
   for row in data['rows']:
    val=eval_poly(row,data,xx)
    if row['name']=='F':assert val<0;continue
    assert val>=0,(name,row['name'],val);rowchecks+=1
   rec.append({'source':name,'type':typ,'norm_coupling':extra,'height_assumption_checked_as': 'false, correctly excluded','root_membership':'not asserted'})
 out={'status':'MODEL_DICTIONARIES_AND_SAME_SOURCE_CONTROLS_PASS','models':audited,'control_cases':len(rec),'nonheight_row_checks':rowchecks,'controls':rec}
 (ROOT/'logs/model_audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='controls'}))
if __name__=='__main__':main()
