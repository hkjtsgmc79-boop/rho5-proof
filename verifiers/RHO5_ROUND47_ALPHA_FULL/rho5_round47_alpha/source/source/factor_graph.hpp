#pragma once
// Exact isolated bounded-rank-one feasibility: explicit signs, exact rational
// multiplicative difference constraints. No logarithms/floating point used.
#include "rankone_oracle.hpp"
using Rat=boost::multiprecision::cpp_rational;
struct Packet {std::vector<BI>a,b;std::vector<std::vector<BI>>z;};
inline bool has_zero(const BI&v){return v.lo<=0&&v.hi>=0;}
inline bool mag_interval(const BI&v,int sign,BI&out){
 if(sign==1)out=v;else out={-v.hi,-v.lo};
 if(out.lo<0)out.lo=0;
 return out.hi>0 && out.lo<=out.hi;
}
struct Edge {int u,v;Rat w;};
inline bool positive_feasible(const std::vector<BI>&a,const std::vector<BI>&b,const std::vector<std::vector<BI>>&z){
 std::vector<Edge>edges;int m=a.size(),n=b.size(),N=m+n+1;
 auto upper=[&](const Big&v) -> Rat {return Rat(v)/Rat(UNIT2);};
 auto reciprocal=[&](const Big&v) -> Rat {return Rat(UNIT2)/Rat(v);};
 for(int i=0;i<m;i++){edges.push_back({0,1+i,upper(a[i].hi)});if(a[i].lo>0)edges.push_back({1+i,0,reciprocal(a[i].lo)});}
 for(int j=0;j<n;j++){edges.push_back({1+m+j,0,upper(b[j].hi)});if(b[j].lo>0)edges.push_back({0,1+m+j,reciprocal(b[j].lo)});}
 for(int i=0;i<m;i++)for(int j=0;j<n;j++){
  edges.push_back({1+m+j,1+i,upper(z[i][j].hi)});
  if(z[i][j].lo>0)edges.push_back({1+i,1+m+j,reciprocal(z[i][j].lo)});
 }
 std::vector<Rat>dist(N,Rat(1));
 for(int t=0;t<N;t++){
  bool changed=false;
  for(const auto&e:edges){Rat cand=dist[e.u]*e.w;if(dist[e.v]>cand){dist[e.v]=std::move(cand);changed=true;}}
  if(!changed)return true;
 }
 return false;
}
inline bool packet_feasible(const Packet&p){
 int m=p.a.size(),n=p.b.size();std::vector<int>il,jr;
 for(const auto&t:p.a)if(empty_i(t))return false;
 for(const auto&t:p.b)if(empty_i(t))return false;
 for(const auto&r:p.z)for(const auto&t:r)if(empty_i(t))return false;
 for(int i=0;i<m;i++){bool forced=!has_zero(p.a[i]);for(int j=0;j<n;j++)forced=forced||!has_zero(p.z[i][j]);if(forced)il.push_back(i);}
 for(int j=0;j<n;j++){bool forced=!has_zero(p.b[j]);for(int i=0;i<m;i++)forced=forced||!has_zero(p.z[i][j]);if(forced)jr.push_back(j);}
 int ml=il.size(),nr=jr.size(),count=ml+nr;if(count>16)throw std::runtime_error("sign enumeration exceeds limit");
 for(unsigned mask=0;mask<(1u<<count);mask++){
  bool ok=true;std::vector<int>sign(count);for(int i=0;i<count;i++)sign[i]=(mask&(1u<<i))?1:-1;
  std::vector<BI>a(ml),b(nr);std::vector<std::vector<BI>>z(ml,std::vector<BI>(nr));
  for(int i=0;i<ml&&ok;i++)ok=mag_interval(p.a[il[i]],sign[i],a[i]);
  for(int j=0;j<nr&&ok;j++)ok=mag_interval(p.b[jr[j]],sign[ml+j],b[j]);
  for(int i=0;i<ml&&ok;i++)for(int j=0;j<nr&&ok;j++)ok=mag_interval(p.z[il[i]][jr[j]],sign[i]*sign[ml+j],z[i][j]);
  if(ok&&positive_feasible(a,b,z))return true;
 }
 return false;
}
inline bool packet_rectangles_pass(const Packet&p){
 int m=p.a.size(),n=p.b.size();
 for(int i=0;i<m;i++)for(int t=i+1;t<m;t++)for(int j=0;j<n;j++)for(int q=j+1;q<n;q++){
  if(rankone_impossible({p.z[i][j],p.z[i][q],p.z[t][j],p.z[t][q]}))return false;
 }
 return true;
}
