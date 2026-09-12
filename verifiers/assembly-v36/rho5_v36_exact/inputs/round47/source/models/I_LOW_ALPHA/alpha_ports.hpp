#pragma once
// Generated from a verified rational wall-flow certificate. No floating comparisons.
// The caller guarantees: only full physical X sources inside this model are being covered.
#include "mc_exact_kernel.hpp"
#include <array>
constexpr long long AC_SCALE=1000000000LL;
constexpr long long AC_OUTER=800000LL;
constexpr long long AC_SPEED=3LL;
constexpr long long AC_RAD=100000LL;
constexpr long long AC_CENTER[4][22]={{2074468372LL,2066258539LL,-2066258539LL,-173343696LL,-2074468372LL,1000000000LL,-47361589LL,1453224662LL,1000000000LL,617532517LL,1000000000LL,779150644LL,453224662LL,1000000000LL,973563295LL,1000000000LL,-581690673LL,453224662LL,194705107LL,-638113324LL,-1279880966LL,879763265LL},{2074468372LL,2066258539LL,-2066258539LL,-2074468372LL,-173343696LL,1000000000LL,47361589LL,1453224662LL,1000000000LL,617532517LL,1000000000LL,779150644LL,-453224662LL,1000000000LL,973563295LL,-1000000000LL,-581690673LL,194705107LL,453224662LL,-638113324LL,879763265LL,-1279880966LL},{2074468372LL,2066258539LL,-2066258539LL,-173343696LL,2074468372LL,-47361589LL,1000000000LL,1453224662LL,1000000000LL,617532517LL,1000000000LL,453224662LL,779150644LL,1000000000LL,1000000000LL,973563295LL,-581690673LL,453224662LL,-194705107LL,-638113324LL,-1279880966LL,-879763265LL},{2074468372LL,2066258539LL,-2066258539LL,-2074468372LL,173343696LL,47361589LL,1000000000LL,1453224662LL,1000000000LL,617532517LL,1000000000LL,-453224662LL,779150644LL,1000000000LL,-1000000000LL,973563295LL,-581690673LL,194705107LL,-453224662LL,-638113324LL,879763265LL,1279880966LL}};
inline const Big ALPHA_LOW_NUM("413251707863247285422334685327737126995279153779908769454418052196743783429681764825855179985483022630152515659887825271609554209934703653072223897312925069088264378769458915450759171541549166637560269");
inline const Big ALPHA_LOW_DEN("100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000");
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
