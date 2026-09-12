from pathlib import Path
from fractions import Fraction as Q
import json,sys,time
ROOT=Path(__file__).parent
sys.path.insert(0,str(ROOT/'inputs/round47/source'))
import native
from gap_model import NAMES,check_actual,physical_matrix,height
from support.x_local_model import wall_transform
from b_tail_envelope import maximize_tail,interpolation

def contract(z,eta):
 z=list(map(Q,z));eta=Q(eta);a=1-eta;b=1-2*eta;d=1-3*eta;f=[b,d,d];o=z[:]
 o[0]=b*b*z[0];o[1]=d*d*z[1];o[2]=d*d*z[2];o[3]=b*d*z[3];o[4]=b*d*z[4];o[5]=d/b*z[5];o[6]=d/b*z[6]
 o[7]=a*a*z[7];o[8]=a*z[8];o[9]=a*z[9]
 for i in range(3):
  o[10+i]=f[i]*z[10+i];o[13+i]=f[i]/a*z[13+i];o[16+i]=f[i]*z[16+i];o[19+i]=a*f[i]*z[19+i]
 o[22]=d*d*z[22];o[23]=d*d*z[23]
 return o

def flags(z):
 z=list(map(Q,z));k,r,w,A,B,c,d=z[:7];a=A/k;b=B/k;s=r-z[22];t=r-z[23];u=z[10:13];v=z[16:19]
 return {'RL':r*a*c>=0 and t*a*d>=0 and r*t*c*d>=0 and r*t*u[1]*u[2]<=0,
 'RR':r*a*c>=0 and s*b*c>=0 and r*s*a*b>=0 and r*s*v[1]*v[2]<=0,
 'SL':s*b*c>=0 and w*b*d>=0 and s*w*c*d>=0 and s*w*u[1]*u[2]<=0,
 'SR':t*a*d>=0 and w*b*d>=0 and t*w*a*b>=0 and t*w*v[1]*v[2]<=0}
def rank2(a,b):return any(a[i]*b[j]!=a[j]*b[i]for i in range(3)for j in range(i+1,3))
def main():
 start=time.monotonic();cert=json.loads((ROOT/'two_gap_certificate.json').read_text());data=json.loads((ROOT/'inputs/round47/source/control_witnesses.json').read_text());base=native.from_matrix(data['base_matrix'])
 assert base[1]+base[2]==0
 cols=[i for i,n in enumerate(NAMES)if n!='p'];gamma=Q(4132517,10**6);al=Q(json.loads((ROOT/'inputs/round47/source/alpha.json').read_text())['isolating_interval']['lower'])
 rec=[];pathcount=0
 for case in cert['cases']:
  c=case['case'];z=wall_transform(base,c,inverse=True)+[Q(0),Q(0)]
  C=[list(map(Q,row))for row in case['preconditioner']];a=case['active_labels'];h=Q(1,10**8)
  for j,col in enumerate(cols):z[col]+=h*(C[j][a.index('sigma')]+C[j][a.index('tau')])
  z[2]=-z[1];z[22]=h;z[23]=h
  z=contract(z,Q(1,10**10));w=check_actual(z)
  assert z[2]==-z[1] and 0<z[22]<z[1] and 0<z[23]<z[1]
  assert gamma<height(z)<al and height(z)+(z[22]+z[23])/10<al
  assert rank2(z[10:13],z[13:16]) and rank2(z[16:19],z[19:22])
  assert not any(flags(z).values()),flags(z)
  cen=list(map(Q,case['center']));dist=max(abs(t-v)for t,v in zip(z,cen));cost=dist+3*(z[22]+z[23]);assert cost<Q(1,1250)
  end=maximize_tail(z)
  for th in (Q(0),Q(1,4),Q(1,2),Q(3,4),Q(1)):interpolation(z,th);pathcount+=1
  rec.append({'case':c,'parameters':list(map(str,z)),'matrix':w['matrix'],'pivots':w['pivots'],'F':str(height(z)),
    'F_display':float(height(z)),'gamma_less_than_F_less_than_alpha_lower':True,'proper_B22':True,'flags':flags(z),
    'two_gap_flow_condition_lhs':str(cost),'r_plus_w':str(z[1]+z[2]),'sigma':str(z[22]),'tau':str(z[23]),
    'tail_envelope_height':str(end['height']),'tail_envelope_display':float(end['height']),'tail_envelope_face':end['paid_face'],
    'tail_envelope_contacts':{t:end[t]for t in ('r_contacts','s_contacts','t_contacts')}})
 out={'status':'V36_FOUR_EXACT_PROPER_B_GAMMA_ABOVE_CONTROLS_PASS','controls':rec,'full_tail_envelope_path_checks':pathcount,'note':'Euler proposals independently checked after contraction; no numerical trajectory proof claimed','seconds':time.monotonic()-start}
 (ROOT/'evidence/proper_B_controls.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='controls'},indent=2))
 for r in rec:print('case',r['case'],'F',r['F_display'],'envelope',r['tail_envelope_display'],'face',r['tail_envelope_face'],flush=True)
if __name__=='__main__':main()
