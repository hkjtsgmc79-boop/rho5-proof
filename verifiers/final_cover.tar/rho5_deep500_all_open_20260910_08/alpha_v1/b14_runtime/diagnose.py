from pathlib import Path
from fractions import Fraction as Q
import sys,json
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'support'))
from exact_interval import I,serial
import structural_rules as sr
# centers literally copied from frozen V43 text, which inherited V36 unchanged
centers0=[['518617093/250000000','2066258539/1000000000','-2066258539/1000000000','-10833981/62500000','-518617093/250000000',1,'-47361589/1000000000','726612331/500000000',1,'617532517/1000000000',1,'194787661/250000000','226612331/500000000',1,'194712659/200000000',1,'-581690673/1000000000','226612331/500000000','194705107/1000000000','-159528331/250000000','-639940483/500000000','175952653/200000000',0,0],
['518617093/250000000','2066258539/1000000000','-2066258539/1000000000','-518617093/250000000','-10833981/62500000',1,'47361589/1000000000','726612331/500000000',1,'617532517/1000000000',1,'194787661/250000000','-226612331/500000000',1,'194712659/200000000',-1,'-581690673/1000000000','194705107/1000000000','226612331/500000000','-159528331/250000000','175952653/200000000','-639940483/500000000',0,0],
['518617093/250000000','2066258539/1000000000','-2066258539/1000000000','-10833981/62500000','518617093/250000000','-47361589/1000000000',1,'726612331/500000000',1,'617532517/1000000000',1,'226612331/500000000','194787661/250000000',1,1,'194712659/200000000','-581690673/1000000000','226612331/500000000','-194705107/1000000000','-159528331/250000000','-639940483/500000000','-175952653/200000000',0,0],
['518617093/250000000','2066258539/1000000000','-2066258539/1000000000','-518617093/250000000','10833981/62500000','47361589/1000000000',1,'726612331/500000000',1,'617532517/1000000000',1,'-226612331/500000000','194787661/250000000',1,-1,'194712659/200000000','-581690673/1000000000','194705107/1000000000','-226612331/500000000','-159528331/250000000','175952653/200000000','639940483/500000000',0,0]]
centers=[[Q(s) for s in c] for c in centers0]
(ROOT/'centers.json').write_text(json.dumps([[str(v)for v in c]for c in centers],indent=2))
A=Q('4.13251707863247285422334685327737126995')
rows=[]
for rec in json.loads((ROOT/'SOURCE_REBUILD.json').read_text())['records']:
 x=sr.image(rec['aux_image']);candidates=[];b9=[];quals=[]
 for name,y in sr.representations(x):
  sig=y['r']-y['s'];tau=y['r']-y['t']
  
  if sig.hi<0 or tau.hi<0:raise ValueError('Physical gap enclosure empty')
  sig=I(max(Q(0),sig.lo),sig.hi);tau=I(max(Q(0),tau.lo),tau.hi)
  gap=[y['k'],y['r'],-y['r']]+[y[n] for n in sr.ORDER[4:23]]+[sig,tau]
  for j,c in enumerate(centers):
   distances=[max(abs(v.lo-a),abs(v.hi-a))for v,a in zip(gap,c)]
   budget=max(distances)+3*(sig.hi+tau.hi)
   candidates.append({'rep':name,'center':j,'budget':budget,'distance':max(distances),'gap_sum':sig.hi+tau.hi,'worst_coord':distances.index(max(distances)),'status':'ALPHA_SAFE'if budget<Q(1,1250)else'OPEN'})
  # qualify proposed directions A/B; keep each fixed representation with actual intervals
  base={'p>=1':y['p']-1,'e>=0':y['e'],'e<=1':1-y['e'],'beta>=0':y['beta'],'beta<=1':1-y['beta'],'v0>=0':y['v0'],'u0>=0':y['u0'],'u2>=0':y['u2'],'x0-u0>=0':y['x0']-y['u0'],'-x2>=0':-y['x2']}
  ag={**base,'u1>=0':y['u1'],'x1-u1>=0':y['x1']-y['u1']}
  bg={'x0>=0':y['x0'],'-x2>=0':-y['x2'],'u2>=0':y['u2'],'d(A-B)>=0':y['d']*(y['A']-y['B'])}
  quals.append({'rep':name,'B13_failed':[k for k,v in base.items()if v.lo<0],'A_WITH_B13_failed':[k for k,v in ag.items()if v.lo<0],'B_failed':[k for k,v in bg.items()if v.lo<0]})
  for typ in ['B09','B10_MINUS']:
   res=sr.old_budget(y,A,typ)
   if res['status']!='OPEN_QUALIFICATION':b9.append({'rep':name,**res})
 best=min(candidates,key=lambda c:c['budget'])
 print('CASE',rec['ordinal'],rec['index'],rec['absolute_depth'],'BEST',serial(best),'GUARDS_B13_A_B',[sum(not q[f+'_failed'] for q in quals)for f in ('B13','A_WITH_B13','B')],flush=True)
 print('B09/10 qualified:',[(r['rep'],r['rule'],r['status'],[float(r['alpha_residual'].lo),float(r['alpha_residual'].hi)]if 'alpha_residual'in r else '')for r in b9],flush=True)
 rows.append({'ordinal':rec['ordinal'],'index':rec['index'],'depth':rec['absolute_depth'],'best':best,'candidates':candidates,'qualifications':quals,'b09_b10':b9})
(ROOT/'DIAGNOSTIC.json').write_text(json.dumps(serial(rows),ensure_ascii=False,indent=2)+'\n')
