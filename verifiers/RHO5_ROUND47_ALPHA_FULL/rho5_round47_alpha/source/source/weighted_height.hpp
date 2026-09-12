#pragma once
#include "mc_exact_kernel.hpp"
#include "alpha_ports.hpp"
// Exact positive row combinations certify an upper bound for F=r-w.
inline Big weighted_height_margin(const EBox&b,const std::vector<std::pair<int,long long>>&weights,long long t){
 if(t<=0||weights.empty()||weights.size()>EB+4*epairs.size())throw std::runtime_error("bad height certificate");
 std::array<Big,EN>co{},lo,hi;Big rhs=0;std::vector<bool>seen(EB+4*epairs.size(),false);
 for(auto[row,w]:weights){
  if(row<0||row>=(int)seen.size()||seen[row])throw std::runtime_error("invalid/duplicate height row");
  seen[row]=true;add_exact_row(b,row,Big(w),co,rhs);
 }
 co[1]-=Big(t)*UNIT;co[2]+=Big(t)*UNIT;
 product_bounds(b,lo,hi);
 for(int j=0;j<EN;j++)rhs-=co[j]*(co[j]>=0?lo[j]:hi[j]);
 return rhs*ALPHA_LOW_DEN-Big(t)*ALPHA_LOW_NUM*UNIT2;
}
