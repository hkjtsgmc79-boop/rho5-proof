#pragma once
// Exact fixed-grid interval arithmetic. All calculations use signed integers.
// Endpoints represent multiples of 2^-32. Rounding always enlarges the interval.
#include <array>
#include <vector>
#include <cstdint>
#include <limits>
#include <utility>
#include <algorithm>
#include <stdexcept>
using Z=std::int64_t;using W=__int128_t;
static constexpr int NV=24;
static constexpr Z SCALE=Z(1)<<32;
static constexpr Z INF=Z(1)<<62;
struct I {Z l,h;I():l(-INF),h(INF){}I(Z a,Z b):l(a),h(b){}};
struct Node{int op,a,b;Z value;};
inline Z enclose(W a,bool upper){
 if(a>=INF)return upper?INF:INF-1;
 if(a<=-W(INF))return upper?-INF+1:-INF;
 return Z(a);
}
inline W fdiv(W a,W b){if(b<=0)throw std::runtime_error("nonpositive floor denominator");W q=a/b,r=a%b;return q-(r<0);}
inline W cdiv(W a,W b){if(b<=0)throw std::runtime_error("nonpositive ceil denominator");W q=a/b,r=a%b;return q+(r>0);}
inline Z add_end(Z a,Z b,bool upper){
 if((a==INF&&b==-INF)||(a==-INF&&b==INF))return upper?INF:-INF;
 if(a==INF||b==INF)return INF;if(a==-INF||b==-INF)return -INF;return enclose(W(a)+b,upper);
}
inline I plus(I a,I b){return I(add_end(a.l,b.l,false),add_end(a.h,b.h,true));}
inline I minus(I a,I b){return plus(a,I(-b.h,-b.l));}
inline Z prod_end(Z a,Z b,bool upper){
 if(a==0||b==0)return 0;
 if(a==INF||a==-INF||b==INF||b==-INF)return ((a>0)==(b>0))?INF:-INF;
 W n=W(a)*W(b);return enclose(upper?cdiv(n,SCALE):fdiv(n,SCALE),upper);
}
inline I times(I a,I b){
 std::array<std::pair<Z,Z>,4> p={{{a.l,b.l},{a.l,b.h},{a.h,b.l},{a.h,b.h}}};
 Z l=INF,h=-INF;for(auto z:p){l=std::min(l,prod_end(z.first,z.second,false));h=std::max(h,prod_end(z.first,z.second,true));}return I(l,h);
}
inline Z rec_end(Z a,bool upper){if(a==INF||a==-INF)return 0;if(a==0)throw std::runtime_error("zero reciprocal");W n=W(SCALE)*SCALE,b=a;if(b<0){n=-n;b=-b;}return enclose(upper?cdiv(n,b):fdiv(n,b),upper);}
inline I divide(I a,I b){if(b.l<=0&&b.h>=0)return I();return times(a,I(rec_end(b.h,false),rec_end(b.l,true)));}
inline bool meet(I& a,I b){a.l=std::max(a.l,b.l);a.h=std::min(a.h,b.h);return a.l<=a.h;}
struct Box{std::array<I,NV>x;unsigned depth=0;};
// Returns true only after deriving an empty interval. Bounds are all necessary
// consequences of the supplied polynomial equations/inequalities and the box.
inline bool contract(Box& box,const std::vector<Node>& spec,const std::vector<std::pair<int,int>>& roots){
 std::vector<I> z(spec.size());for(int i=0;i<NV;i++)z[i]=box.x[i];
 for(int it=0;it<100;it++){
  std::array<I,NV> old;for(int i=0;i<NV;i++)old[i]=z[i];
  for(std::size_t i=NV;i<spec.size();i++){
   const auto& n=spec[i];I val;
   if(n.op==1)val=I(n.value,n.value);
   else if(n.op==2)val=plus(z[n.a],z[n.b]);
   else if(n.op==3)val=times(z[n.a],z[n.b]);
   else throw std::runtime_error("invalid opcode");
   if(!meet(z[i],val))return true;
  }
  for(auto root:roots){if(!meet(z[root.first],root.second?I(0,0):I(0,INF)))return true;}
  for(int i=int(spec.size())-1;i>=NV;i--){
   const auto& n=spec[i];
   if(n.op==2){if(!meet(z[n.a],minus(z[i],z[n.b])))return true;if(!meet(z[n.b],minus(z[i],z[n.a])))return true;}
   else if(n.op==3){if(!meet(z[n.a],divide(z[i],z[n.b])))return true;if(!meet(z[n.b],divide(z[i],z[n.a])))return true;}
  }
  bool changed=false;for(int i=0;i<NV;i++)if(z[i].l>old[i].l+SCALE/1000000||z[i].h<old[i].h-SCALE/1000000)changed=true;
  if(!changed)break;
 }
 for(int i=0;i<NV;i++)box.x[i]=z[i];return false;
}
