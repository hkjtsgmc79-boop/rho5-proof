"""Frozen mathematical models for NEXT proper-B alpha coverage.
No B whole-root proof tree or production parallel search engine is supplied here.
Each of 54 models inherits this same full source and adds three actual contact equalities.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import json,hashlib
ROOT=Path(__file__).parent
NAMES=('k','r','s','t','A','B','c','d','p','e','beta')+tuple(a+str(i)for a in ('u','x','v','q')for i in range(3))+('F',)

def plus(*ps):
 d={}
 for p in ps:
  for m,a in p.items():d[m]=d.get(m,Q(0))+a
 return {m:a for m,a in d.items()if a}
def times(p,q):
 d={}
 for m,a in p.items():
  for n,b in q.items():t=tuple(sorted(m+n));d[t]=d.get(t,Q(0))+a*b
 return {m:a for m,a in d.items()if a}
def scale(p,a):return {m:c*Q(a)for m,c in p.items()if c*a}
def constant(a):return {():Q(a)}if a else{}
def var(n):return {(NAMES.index(n),):Q(1)}
def evaluate(p,z):
 ans=Q(0)
 for mon,c in p.items():
  for i in mon:c*=z[i]
  ans+=c
 return ans

def source():
 z={n:var(n)for n in NAMES};k,r,s,t,A,B,c,d,p,e,be=[z[n]for n in NAMES[:11]]
 u,x,v,q=[[z[a+str(i)]for i in range(3)]for a in ('u','x','v','q')]
 D=[[k,A,B],[times(c,k),plus(r,times(c,A)),plus(s,times(c,B))],[times(d,k),plus(t,times(d,A)),plus(scale(r,-1),times(d,B))]]
 S=[[plus(D[i][j],times(x[i],q[j]))for j in range(3)]for i in range(3)]
 O=[[plus(S[i][j],times(u[i],v[j]))for j in range(3)]for i in range(3)]
 rows={};one=constant(1)
 def band(a,b,n):
  for sign,tag in [(-1,'+'),(1,'-')]:
   row=plus(b,scale(a,sign))
   if row:rows[n+tag]=row
 band(e,one,'e');band(be,one,'beta');band(plus(p,scale(times(e,be),-1)),one,'head')
 for i in range(3):
  for a,b,n in [(u[i],one,'u'),(x[i],one,'x'),(v[i],one,'v'),(q[i],p,'q')]:band(a,b,n+str(i))
  band(plus(times(p,x[i]),scale(times(e,u[i]),-1)),one,'L'+str(i))
  band(plus(q[i],times(be,v[i])),one,'P'+str(i))
  for j in range(3):
   for mat,cap,name in [(D,k,'D'),(S,p,'S'),(O,one,'O')]:band(mat[i][j],cap,name+str(i)+str(j))
 rows.update({'r-s':plus(r,scale(s,-1)),'r-t':plus(r,scale(t,-1)),
  'F_trigger':plus(z['F'],constant(-Q(4132517,10**6))),
  'Fcore':plus(scale(k,Q(9,4)),scale(z['F'],-1)),
  'Ffirst':plus(scale(p,4),scale(z['F'],-1)),
  'Ftail':plus(scale(r,2),scale(z['F'],-1)),
  'det3':plus(constant(4),scale(times(p,k),-1)),
  'k-2p':plus(scale(p,2),scale(k,-1)),
  'r-2k':plus(scale(k,2),scale(r,-1))})
 eq=plus(times(r,z['F']),scale(times(r,r),-1),scale(times(s,t),-1));rows['height_eq+']=eq;rows['height_eq-']=scale(eq,-1)
 return rows

def payload():
 gamma=Q(4132517,10**6)
 lo={'k':4*gamma/9,'r':gamma/2,'s':0,'t':0,'A':Q(-9,4),'B':Q(-9,4),'c':-1,'d':-1,'p':gamma/4,'e':gamma/4-1,'beta':gamma/4-1,'F':gamma}
 hi={'k':Q(9,4),'r':4,'s':4,'t':4,'A':0,'B':Q(9,4),'c':1,'d':1,'p':2,'e':1,'beta':1,'F':8}
 for a in ('u','x','v','q'):
  for i in range(3):lo[a+str(i)]=-2 if a=='q' else -1;hi[a+str(i)]=2 if a=='q' else 1
 lo['x0']=0
 rows=source();assert all(len(mon)<=2 for p in rows.values()for mon in p)
 serialize=lambda p:[{'monomial':list(m),'coefficient':str(a)}for m,a in sorted(p.items())]
 return {'schema':'V36_PROPER_B_CONTACT_MODEL_V1','coordinate_order':list(NAMES),
  'scope':'same complete real normalized negative D-chart; r>0, 0<=s,t<=r, F=r+s*t/r',
  'bounds':{n:[str(Q(lo[n])),str(Q(hi[n]))]for n in NAMES},'rows_ge_zero':{n:serialize(p)for n,p in rows.items()},
  'all_closed_faces_retained':True,
  'alpha_sha256':hashlib.sha256((ROOT/'inputs/round47/source/alpha.json').read_bytes()).hexdigest(),
  'two_gap_certificate_sha256':hashlib.sha256((ROOT/'two_gap_certificate.json').read_bytes()).hexdigest(),
  'assembly_scope':'frozen full X theorem, exact R/S/T transports; no general five-by-five upper theorem','normalization':'e,beta positive; x0>=0; A<=0; no sign assumed on other receivers, B,c,d',
  'lower_trigger_only':'4132517/1000000','final_target':'exact alpha; gamma is NOT an upper cap',
  'explicit_low_order_inputs':['real complete-pivot rho3=9/4','real complete-pivot rho4=4'],
  'safe_outlets':['full X / solved S,T faces','V36 two-gap flow region','exact rational height upper bound <=alpha_lower'],
  'forbidden_imports':['V31 k<=2 X bound on proper B','X r-w objective','X strict-high-r exclusions','X-specific necessary rows or head type guard without scope proof'],
  'global_coverage_status':'OPEN; no search or complete B tree supplied'}

def main():
 out=ROOT/'next_B_models';out.mkdir(exist_ok=True);base=payload();raw=json.dumps(base,indent=2)+'\n';(out/'base_model.json').write_text(raw)
 h=hashlib.sha256(raw.encode()).hexdigest();rs=['D11+','S11+','O11+','D22-','S22-','O22-'];ss=['D12+','S12+','O12+'];ts=['D21+','S21+','O21+']
 carriers=[]
 for i,(a,b,c)in enumerate(product(rs,ss,ts)):
  carriers.append({'id':f'B_CONTACT_{i:02d}','base_model_sha256':h,'additional_equal_zero':[a,b,c],
   'implementation':'retain base row g>=0 and append -g>=0 for each listed physical slack',
   'strict_source_phase':'s<r and t<r; modeled by closed outer domain, equality faces safe by S/T',
   'status':'OPEN'})
 (out/'contacts54.json').write_text(json.dumps({'base_model_sha256':h,'count':54,'type':'finite covering, not disjoint; all tied selectors retained','models':carriers},indent=2)+'\n')
 representatives=[z for z in carriers if ['D','S','O'].index(z['additional_equal_zero'][1][0])<=['D','S','O'].index(z['additional_equal_zero'][2][0])]
 assert len(representatives)==36
 (out/'representatives36.json').write_text(json.dumps({'base_model_sha256':h,'count':36,'selection':'s_upper_layer <= t_upper_layer in D,S,O order','proof':'actual normalized transpose exchanges s/t layers, preserves r-provider and full source','models':representatives},indent=2)+'\n')
 print(json.dumps({'symmetry_representatives':len(representatives),'status':'V36_NEXT_B_MODELS_FROZEN_NOT_SOLVED','actual_variables':len(NAMES),'base_rows':len(base['rows_ge_zero']),'contact_models':len(carriers),'base_sha256':h}))
if __name__=='__main__':main()
