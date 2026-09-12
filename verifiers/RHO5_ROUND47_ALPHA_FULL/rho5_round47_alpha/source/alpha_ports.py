"""Source-conditioned alpha-safe box exits. These are NOT infeasibility tests.
A 0..3: four certified local physical wall flows.
A 4: complete physical weak R0 region (frozen R0-alpha theorem).
A 5: F<=2r<=the exact rational lower endpoint of the frozen alpha isolator.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,hashlib
from local_model import NAMES,canonical_requirements
ROOT=Path(__file__).resolve().parent

def product_iv(a,b):
 v=[a[i]*b[j] for i in (0,1) for j in (0,1)];return min(v),max(v)
def poly_iv(poly,box):
 lo=hi=Q(0)
 for mon,c in poly.items():
  a=b=c
  for i in mon:a,b=product_iv((a,b),box[i])
  lo+=a;hi+=b
 return lo,hi

def data():return json.loads((ROOT/'local_wall_certificate.json').read_text())
def proves(box,code,cert=None):
 if len(box)<22 or any(a>b for a,b in box):raise ValueError('invalid box')
 cert=cert or data()
 if code in range(4):
  rad=Q(cert['inner_radius']);cen=list(map(Q,cert['cases'][code]['center']))
  return all(c-rad<=box[i][0]<=box[i][1]<=c+rad for i,c in enumerate(cen))
 if code==4:return all(poly_iv(p,box)[0]>=0 for p in canonical_requirements().values())
 if 7<=code<=10:
  center=list(map(Q,cert['cases'][code-7]['center']))
  radius=Q(cert['outer_radius']);speed=Q(cert['uniform_speed_cap'])
  distance=max(max(abs(l-c),abs(h-c)) for (l,h),c in zip(box,center))
  wall_upper=max(Q(0),box[1][1]+box[2][1])
  return distance+speed*wall_upper<radius
 if code==6:
  alpha=json.loads((ROOT/'alpha.json').read_text());a=Q(alpha['isolating_interval']['lower'])
  return box[1][1]-box[2][0]<=a
 if code==5:
  alpha=json.loads((ROOT/'alpha.json').read_text());a=Q(alpha['isolating_interval']['lower'])
  return 2*box[1][1]<=a
 raise ValueError('unknown safe-exit code')

def find(box):
 for i in range(11):
  if proves(box,i):return i
 return -1

def write_header(model,path):
 path=Path(path);cert=data()
 rule=json.loads((ROOT/'DIRECT_F_RULE.json').read_text())
 expected={'schema': 'CQG_V35_DIRECT_F_EXIT_V1', 'code': 6, 'coordinate_order_prefix': ['k', 'r', 'w'], 'F_definition': 'r-w', 'whole_box_upper_bound': 'r_upper-w_lower', 'threshold': 'alpha.json isolating_interval.lower', 'alpha_definition_sha256': '9af09b9d6e584bba2a7cef7e9e3993f128fbc90744335eb0c22c8b11e0226959', 'acceptance': '(r_upper-w_lower)*ALPHA_LOW_DEN <= ALPHA_LOW_NUM*UNIT', 'meaning': 'alpha safety, not contradiction; all original-root siblings remain unpaid unless separately certified', 'flow_tube_codes': [7, 8, 9, 10], 'flow_tube_domain': 'max_i|z_i-center_i| + speed*max(0,r+w) < outer_radius', 'flow_tube_certificate_sha256': '5d43a6936c0fe574d13ebc5c90ecd5762990bf64f2a358cfe4106eb210f8f132', 'flow_tube_meaning': 'F <= alpha - uniform_height_gain*(r+w), using the original outer-box flow certificate'}
 if rule!=expected:raise ValueError('Unrecognized direct F theorem definition')
 if Q(cert['outer_radius'])!=Q(1,1250) or Q(cert['uniform_speed_cap'])!=3:raise ValueError('Unsupported flow constants')
 if rule['flow_tube_certificate_sha256']!=hashlib.sha256((ROOT/'local_wall_certificate.json').read_bytes()).hexdigest():raise ValueError('Unbound outer certificate')
 if model.get('additional_alpha_rule_sha256')!=hashlib.sha256((ROOT/'DIRECT_F_RULE.json').read_bytes()).hexdigest():raise ValueError('Unbound direct F theorem')
 from verify_local_certificate import verify
 verify(cert)
 names=['beta' if n=='be' else n for n in model['variables'][:22]]
 if names!=list(NAMES):raise ValueError('native coordinate order mismatch')
 h=hashlib.sha256((ROOT/'local_wall_certificate.json').read_bytes()).hexdigest()
 if model.get('alpha_ports_certificate_sha256')!=h:raise ValueError('unbound alpha local certificate')
 alpha=json.loads((ROOT/'alpha.json').read_text());al=Q(alpha['isolating_interval']['lower']);au=Q(alpha['isolating_interval']['upper'])
 if not Q(model['target'])<al<au:raise ValueError('trigger/alpha order')
 scale=10**9;rad=Q(cert['inner_radius'])*scale
 if rad.denominator!=1:raise ValueError('unsupported exact radius denominator')
 cn=[]
 for case in cert['cases']:
  row=[Q(v)*scale for v in case['center']]
  if any(v.denominator!=1 for v in row):raise ValueError('unsupported exact center denominator')
  cn.append([int(v) for v in row])
 text='''#pragma once
// Generated from a verified rational wall-flow certificate. No floating comparisons.
// The caller guarantees: only full physical X sources inside this model are being covered.
#include "mc_exact_kernel.hpp"
#include <array>
constexpr long long AC_SCALE=1000000000LL;
constexpr long long AC_OUTER=800000LL;
constexpr long long AC_SPEED=3LL;
constexpr long long AC_RAD=__RAD__LL;
constexpr long long AC_CENTER[4][22]={__CENTERS__};
inline const Big ALPHA_LOW_NUM("__ALNUM__");
inline const Big ALPHA_LOW_DEN("__ALDEN__");
inline std::pair<Big,Big> alpha_mul_interval(const EBox& b,int i,int j){
 std::array<Big,4> x{Big(b.lo[i]*b.lo[j]),Big(b.lo[i]*b.hi[j]),Big(b.hi[i]*b.lo[j]),Big(b.hi[i]*b.hi[j])};
 return {*std::min_element(x.begin(),x.end()),*std::max_element(x.begin(),x.end())};
}
inline bool alpha_exit_proves(const EBox&b,int code){
 if(code>=0&&code<4){
  for(int i=0;i<22;i++)if(b.lo[i]*AC_SCALE<Big(AC_CENTER[code][i]-AC_RAD)*UNIT||b.hi[i]*AC_SCALE>Big(AC_CENTER[code][i]+AC_RAD)*UNIT)return false;
  return true;
 }
 if(code==4){
  for(int i:{9,10,11,12,13,14,15})if(b.lo[i]<0)return false;
  for(int i:{3,4,6})if(b.hi[i]>0)return false;
  if(b.lo[10]*UNIT-alpha_mul_interval(b,9,13).second<0)return false;
  if(b.lo[11]*UNIT-alpha_mul_interval(b,9,14).second<0)return false;
  if(alpha_mul_interval(b,9,15).first-b.hi[12]*UNIT<0)return false;
  if(alpha_mul_interval(b,10,14).first-alpha_mul_interval(b,13,11).second<0)return false;
  if(alpha_mul_interval(b,10,15).first-alpha_mul_interval(b,13,12).second<0)return false;
  if(alpha_mul_interval(b,11,15).first-alpha_mul_interval(b,14,12).second<0)return false;
  return true;
 }
 if(code>=7&&code<=10){
  int j=code-7;Big distance=0;Big du=b.hi[1]+b.hi[2];if(du<0)du=0;
  for(int i=0;i<22;i++){
   Big a=Big(b.lo[i]*AC_SCALE)-Big(AC_CENTER[j][i])*UNIT;if(a<0)a=-a;
   Big z=Big(b.hi[i]*AC_SCALE)-Big(AC_CENTER[j][i])*UNIT;if(z<0)z=-z;
   if(a>distance)distance=a;if(z>distance)distance=z;
  }
  return distance+Big(AC_SPEED)*AC_SCALE*du<Big(AC_OUTER)*UNIT;
 }
 if(code==6)return Big(b.hi[1]-b.lo[2])*ALPHA_LOW_DEN<=ALPHA_LOW_NUM*UNIT;
 if(code==5)return Big(2)*b.hi[1]*ALPHA_LOW_DEN<=ALPHA_LOW_NUM*UNIT;
 return false;
}
inline int alpha_exit(const EBox&b){for(int c=0;c<11;c++)if(alpha_exit_proves(b,c))return c;return -1;}
'''
 text=text.replace('__RAD__',str(int(rad))).replace('__CENTERS__',','.join('{'+','.join(str(v)+'LL' for v in row)+'}' for row in cn)).replace('__ALNUM__',str(al.numerator)).replace('__ALDEN__',str(al.denominator))
 (path/'alpha_ports.hpp').write_text(text)
