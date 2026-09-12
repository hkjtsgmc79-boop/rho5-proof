#pragma once
#include "mc_exact_model.hpp"
#include <boost/multiprecision/cpp_int.hpp>
#include <array>
#include <stdexcept>
#include <string>
#include <algorithm>
using Big=boost::multiprecision::cpp_int;
inline const Big UNIT=Big(ROOT_DEN)<<128;
inline const Big UNIT2=UNIT*UNIT;
struct EBox{std::array<Big,EV>lo,hi;int depth=0;};
inline EBox root_box(){EBox b;for(int i=0;i<EV;i++){b.lo[i]=Big(erootlo[i])<<128;b.hi[i]=Big(eroothi[i])<<128;}return b;}
inline std::pair<EBox,EBox> split_box(const EBox&b,int i){
 if(i<0||i>=EV)throw std::runtime_error("bad split index");
 Big sum=b.lo[i]+b.hi[i];if((sum%2)!=0)throw std::runtime_error("exact grid exhausted");
 Big m=sum/2;if(m<=b.lo[i]||m>=b.hi[i])throw std::runtime_error("bad midpoint");
 EBox l=b,h=b;l.hi[i]=m;h.lo[i]=m;l.depth++;h.depth++;return{l,h};
}
inline void product_bounds(const EBox&b,std::array<Big,EN>&lo,std::array<Big,EN>&hi){
 for(int i=0;i<EV;i++){lo[i]=b.lo[i];hi[i]=b.hi[i];}
 for(size_t n=0;n<epairs.size();n++){auto[i,j]=epairs[n];std::array<Big,4> v{b.lo[i]*b.lo[j],b.lo[i]*b.hi[j],b.hi[i]*b.lo[j],b.hi[i]*b.hi[j]};lo[EV+n]=*std::min_element(v.begin(),v.end());hi[EV+n]=*std::max_element(v.begin(),v.end());}
}
// Original variable coefficients have UNIT denominator. Product coefficients are
// integers. All right sides have UNIT^2 denominator. Hence every arithmetic
// operation in a final contradiction is integer arithmetic, without rounding.
inline void add_exact_row(const EBox&b,int row,const Big&w,std::array<Big,EN>&co,Big&rhs){
 if(row<0||row>=EB+4*(int)epairs.size())throw std::runtime_error("bad physical/McCormick row");
 if(w<=0)throw std::runtime_error("weight must be positive");
 if(row<EB){for(int j=0;j<EN;j++)if(ebase[row][j]){Big v=w*ebase[row][j];if(j<EV)v*=UNIT;co[j]+=v;}rhs+=w*erhs[row]*UNIT2;return;}
 int n=(row-EB)/4,t=(row-EB)%4;auto[i,j]=epairs[n];int y=EV+n;
 Big ci,cj,rr;int cy;
 if(t==0){ci=b.lo[j];cj=b.lo[i];cy=-1;rr=b.lo[i]*b.lo[j];}
 else if(t==1){ci=b.hi[j];cj=b.hi[i];cy=-1;rr=b.hi[i]*b.hi[j];}
 else if(t==2){ci=-b.hi[j];cj=-b.lo[i];cy=1;rr=-b.lo[i]*b.hi[j];}
 else{ci=-b.lo[j];cj=-b.hi[i];cy=1;rr=-b.hi[i]*b.lo[j];}
 co[i]+=w*ci;co[j]+=w*cj;co[y]+=w*cy;rhs+=w*rr;
}
inline Big contradiction_margin(const EBox&b,const std::vector<std::pair<int,long long>>&weights){
 if(weights.empty()||weights.size()>EB+4*epairs.size())throw std::runtime_error("bad support size");
 std::array<Big,EN>co{},lo,hi;Big rhs=0;std::vector<bool>seen(EB+4*epairs.size(),false);
 for(auto[row,w]:weights){if(row<0||row>=(int)seen.size()||seen[row])throw std::runtime_error("invalid/duplicate row");seen[row]=true;add_exact_row(b,row,Big(w),co,rhs);}
 product_bounds(b,lo,hi);
 for(int j=0;j<EN;j++)rhs-=co[j]*(co[j]>=0?lo[j]:hi[j]);
 return rhs;
}
