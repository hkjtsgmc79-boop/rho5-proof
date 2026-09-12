from pathlib import Path
import json,sys
from fractions import Fraction as Q
R=Path(__file__).resolve().parent
sys.path.insert(0,str(R/'support'));import structural_rules as sr
from exact_interval import serial

def guards(z):
 common={'p-1':z['p']-1,'e':z['e'],'1-e':1-z['e'],'beta':z['beta'],'1-beta':1-z['beta'],'v0':z['v0']}
 return {
 'B13_BASE':{**common,'u0':z['u0'],'u2':z['u2'],'x0-u0':z['x0']-z['u0'],'-x2':-z['x2']},
 'DIRECTION_A_ONLY':{**common,'u1':z['u1'],'x1-u1':z['x1']-z['u1']},
 'DIRECTION_B_ONLY':{'x0':z['x0'],'-x2':-z['x2'],'u2':z['u2'],'d(A-B)':z['d']*(z['A']-z['B'])}}
rows=[]
for s in json.loads((R/'SOURCE_REBUILD.json').read_text())['records']:
 x=sr.image(s['aux_image']);g0=guards(x);data={n:{'original_failed':[g for g,v in rr.items() if v.lo<0],'certified_reps':[]}for n,rr in g0.items()}
 for tag,y in sr.representations(x):
  for n,rr in guards(y).items():
   if all(v.lo>=0 for v in rr.values()):data[n]['certified_reps'].append(tag)
 row={'ordinal':s['ordinal'],'index':s['index'],'depth':s['absolute_depth'],'rules':data};rows.append(row)
 print(s['ordinal'],data)
(R/'APPLICABILITY.json').write_text(json.dumps(rows,indent=2)+'\n')
