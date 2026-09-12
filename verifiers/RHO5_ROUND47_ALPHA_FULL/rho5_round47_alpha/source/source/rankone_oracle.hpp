#pragma once
// Exact necessary interval contraction on three ACTUAL rank-one tail packets.
// Every endpoint has denominator UNIT2; determinant products have UNIT2^2.
// No optimization, floating point, division, or rounding occurs in this file.
#include "mc_exact_kernel.hpp"
struct BI {Big lo,hi;};
inline BI plus_i(const BI&a,const BI&b){return{a.lo+b.lo,a.hi+b.hi};}
inline BI minus_i(const BI&a,const BI&b){return{a.lo-b.hi,a.hi-b.lo};}
inline BI meet_i(const BI&a,const BI&b){return{std::max(a.lo,b.lo),std::min(a.hi,b.hi)};}
inline bool empty_i(const BI&a){return a.lo>a.hi;}
inline BI times_i(const BI&a,const BI&b){std::array<Big,4>v{a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi};return{*std::min_element(v.begin(),v.end()),*std::max_element(v.begin(),v.end())};}
inline BI var_i(const EBox&b,int i){return{b.lo[i]*UNIT,b.hi[i]*UNIT};}
inline BI raw_product_i(const EBox&b,int i,int j){std::array<Big,4>v{b.lo[i]*b.lo[j],b.lo[i]*b.hi[j],b.hi[i]*b.lo[j],b.hi[i]*b.hi[j]};return{*std::min_element(v.begin(),v.end()),*std::max_element(v.begin(),v.end())};}
inline bool rankone_impossible(const std::array<BI,4>&z){
 for(const auto&a:z)if(empty_i(a))return true;
 BI a=times_i(z[0],z[3]),b=times_i(z[1],z[2]);
 return a.hi<b.lo || b.hi<a.lo;
}
inline int rankone_exclusion(const EBox&b){
 static_assert(EV>=22,"native variable dictionary required");
 const Big p=b.hi[7]*UNIT,k=b.hi[0]*UNIT;
 if(p<0||k<0)throw std::runtime_error("oracle requires nonnegative p,k upper bounds");
 const BI pb{-p,p},kb{-k,k},one{-UNIT2,UNIT2};
 std::array<BI,4>h,core,stage,orig,ds,ss,oo;
 for(int i=1;i<=2;i++)for(int j=1;j<=2;j++){
  int n=2*(i-1)+j-1;
  h[n]=var_i(b,(i==2&&j==2)?2:1);
  core[n]=meet_i(raw_product_i(b,4+i,2+j),kb);
  stage[n]=meet_i(raw_product_i(b,13+i,19+j),pb);
  orig[n]=meet_i(raw_product_i(b,10+i,16+j),one);
 }
 // These interval contractors preserve every actual source point. A failure
 // of any one interval suffices; return 3 denotes such a direct contradiction.
 for(int pass=0;pass<2;pass++){
  for(int n=0;n<4;n++){
   ds[n]=meet_i(plus_i(h[n],core[n]),kb);
   ss[n]=meet_i(plus_i(ds[n],stage[n]),pb);
   oo[n]=meet_i(plus_i(ss[n],orig[n]),one);
   if(empty_i(core[n])||empty_i(stage[n])||empty_i(orig[n])||empty_i(ds[n])||empty_i(ss[n])||empty_i(oo[n]))return 3;
   orig[n]=meet_i(orig[n],minus_i(oo[n],ss[n]));
   ss[n]=meet_i(ss[n],minus_i(oo[n],orig[n]));
   stage[n]=meet_i(stage[n],minus_i(ss[n],ds[n]));
   ds[n]=meet_i(ds[n],minus_i(ss[n],stage[n]));
   core[n]=meet_i(core[n],minus_i(ds[n],h[n]));
   if(empty_i(core[n])||empty_i(stage[n])||empty_i(orig[n])||empty_i(ds[n])||empty_i(ss[n]))return 3;
  }
  if(rankone_impossible(stage))return 0;
  if(rankone_impossible(orig))return 1;
  if(rankone_impossible(core))return 2;
 }
 return -1;
}
