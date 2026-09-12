#include "dyadic_kernel.hpp"
#include MODEL_HEADER
#include "mean_kernel.hpp"
extern "C" int nv(){return NV;}
extern "C" int nr(){int n=0;for(auto r:roots)n+=r.second?2:1;return n;}
// lohi is contracted in-place. c has (nr)*(NV+1) signed fixed-grid integers:
// first NV are derivative centers, last is outward constant error.
extern "C" int assess(long long* lohi,long long* rad,long long* c){
 try {
 Box b;for(int i=0;i<NV;i++)b.x[i]=I(lohi[2*i],lohi[2*i+1]);
 if(contract_all(b))return 1;
 std::vector<I> range(spec.size()),center(BASE_COUNT);std::array<I,NV>disp;std::array<Z,NV> mids;
 for(int i=0;i<NV;i++){lohi[2*i]=b.x[i].l;lohi[2*i+1]=b.x[i].h;Z m=b.x[i].l+(b.x[i].h-b.x[i].l)/2;mids[i]=m;rad[i]=std::max(m-b.x[i].l,b.x[i].h-m);range[i]=b.x[i];center[i]=I(m,m);disp[i]=minus(b.x[i],I(m,m));}
 for(std::size_t i=NV;i<spec.size();i++){range[i]=eval_node(spec[i],range);if(i<BASE_COUNT)center[i]=eval_node(spec[i],center);}
 int row=0;
 for(std::size_t j=0;j<roots.size();j++){
  I er=center[roots[j].first];std::array<Z,NV> cc;
  for(int i=0;i<NV;i++){I g=range[gradrefs[j][i]];if(g.l<=-INF||g.h>=INF)return 2;Z m=g.l+(g.h-g.l)/2;cc[i]=m;er=plus(er,times(minus(g,I(m,m)),disp[i]));}
  if(er.l<=-INF||er.h>=INF)return 2;
  for(int i=0;i<NV;i++)c[row*(NV+1)+i]=cc[i];c[row*(NV+1)+NV]=er.h;row++;
  if(roots[j].second){for(int i=0;i<NV;i++)c[row*(NV+1)+i]=-cc[i];c[row*(NV+1)+NV]=-er.l;row++;}
 }
 return 0;
 }catch(...){return -1;}
}
