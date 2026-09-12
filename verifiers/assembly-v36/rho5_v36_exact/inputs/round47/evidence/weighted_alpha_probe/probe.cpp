#include "mc_model.hpp"
#include "proposal_simplex.hpp"
#include "fast_simplex.hpp"
#include "mc_exact_kernel.hpp"
#include "rankone_oracle.hpp"
#include "factor_oracle.hpp"
#include "alpha_ports.hpp"
#include <fstream>
#include <iostream>
#include <chrono>
#include <iomanip>
#include <cmath>
using Weights=std::vector<std::pair<int,long long>>;

Big weighted_height_margin(const EBox&b,const Weights&weights,long long t){
 if(t<=0||weights.empty()||weights.size()>EB+4*epairs.size())throw std::runtime_error("bad height certificate");
 std::array<Big,EN>co{},lo,hi;Big rhs=0;std::vector<bool>seen(EB+4*epairs.size(),false);
 for(auto[row,w]:weights){if(row<0||row>=(int)seen.size()||seen[row])throw std::runtime_error("bad row");seen[row]=true;add_exact_row(b,row,Big(w),co,rhs);}
 co[1]-=Big(t)*UNIT;co[2]+=Big(t)*UNIT;
 product_bounds(b,lo,hi);
 for(int j=0;j<EN;j++)rhs-=co[j]*(co[j]>=0?lo[j]:hi[j]);
 return rhs*ALPHA_LOW_DEN-Big(t)*ALPHA_LOW_NUM*UNIT2;
}

const double US=UNIT.convert_to<double>();
struct Found{bool closed=false;Weights w;std::vector<double> val;long long height_t=0;Big height_margin=0;double height_lp=0;};
Found solve_box_fast(const EBox &nd){
 std::vector<double>lo(NX),hi(NX),dd(NX);
 for(int j=0;j<NV;j++){lo[j]=nd.lo[j].convert_to<double>()/US;hi[j]=nd.hi[j].convert_to<double>()/US;}
 for(int nn=0;nn<(int)pairs.size();nn++){auto[i,j]=pairs[nn];double t[]={lo[i]*lo[j],lo[i]*hi[j],hi[i]*lo[j],hi[i]*hi[j]};lo[NV+nn]=*std::min_element(t,t+4);hi[NV+nn]=*std::max_element(t,t+4);}
 for(int j=0;j<NX;j++)dd[j]=hi[j]-lo[j];
 std::vector<std::vector<double>>A=base;std::vector<double>b=rhs,scales;
 for(int nn=0;nn<(int)pairs.size();nn++){
  auto[i,j]=pairs[nn];int y=NV+nn;double li=lo[i],ui=hi[i],lj=lo[j],uj=hi[j];
  double vals[4][4]={{lj,li,-1,li*lj},{uj,ui,-1,ui*uj},{-uj,-li,1,-li*uj},{-lj,-ui,1,-ui*lj}};
  for(auto&v:vals){std::vector<double>row(NX);row[i]+=v[0];row[j]+=v[1];row[y]=v[2];A.push_back(row);b.push_back(v[3]);}
 }
 for(size_t i=0;i<A.size();i++){
  double sh=0;for(int j=0;j<NX;j++){sh+=A[i][j]*lo[j];A[i][j]*=dd[j];}b[i]-=sh;
  double sc=std::max(1e-6,std::abs(b[i]));for(auto v:A[i])sc=std::max(sc,std::abs(v));
  scales.push_back(sc);for(auto&v:A[i])v/=sc;b[i]/=sc;
 }
 for(int j=0;j<NX;j++){std::vector<double>row(NX);row[j]=1;A.push_back(row);b.push_back(1);}
 std::vector<double>obj(NX);obj[1]=dd[1];obj[2]=-dd[2];
 FastSimplex lp(A,b,obj);std::vector<double>x;double ans=lp.solve(x);Found out;
 
 out.height_lp=ans+lo[1]-lo[2];
 if(std::isfinite(ans)&&x.size()==NX){
  auto ww=lp.dual();double mx=1;std::vector<double>raw(scales.size());
  for(size_t i=0;i<raw.size();i++){raw[i]=std::max(0.,ww[i])/scales[i];mx=std::max(mx,raw[i]);}
  if(std::isfinite(mx))for(double prec:{1e6,1e9,1e12,1e15,1e18}){
   if(prec/mx<1)continue;long long t=std::llround(prec/mx);Weights w;
   for(size_t i=0;i<raw.size();i++)if(raw[i]>0){long long wi=std::llround(t*raw[i]);if(wi>0)w.push_back({i,wi});}
   if(!w.empty()){Big margin=weighted_height_margin(nd,w,t);if(margin<=0){out.height_t=t;out.height_margin=margin;out.w=w;break;}}
  }
 }

 bool valid=std::isfinite(ans)&&x.size()==NX;
 if(valid)for(int j=0;j<NX;j++)if(!std::isfinite(x[j])||x[j]<-1e-7||x[j]>1+1e-7){valid=false;break;}
 if(valid)for(size_t i=0;i<A.size();i++){
  long double dot=0,mag=1+std::abs(b[i]);
  for(int j=0;j<NX;j++){dot+=(long double)A[i][j]*x[j];mag+=std::abs((long double)A[i][j]*x[j]);}
  if(dot>(long double)b[i]+1e-8L*mag){valid=false;break;}
 }
 if(valid){out.val.resize(NX);for(int j=0;j<NX;j++)out.val[j]=lo[j]+x[j]*dd[j];}
 else{
  auto ww=lp.dual();double mx=0;std::vector<double>raw(scales.size());
  for(size_t i=0;i<raw.size();i++){raw[i]=std::max(0.,ww[i])/scales[i];mx=std::max(mx,raw[i]);}
  if(mx>0&&std::isfinite(mx))for(double prec:{1e6,1e9,1e12,1e15}){
   Weights w;for(size_t i=0;i<raw.size();i++)if(raw[i]>0){long long wi=std::llround(prec*raw[i]/mx);if(wi>0)w.push_back({i,wi});}
   if(!w.empty()&&contradiction_margin(nd,w)<0){out.closed=true;if(!out.height_t)out.w=std::move(w);break;}
  }
 }
 return out;
}

int main(int argc,char**argv){try{
 std::ifstream input(argv[1]);std::string id;int depth;
 while(input>>id>>depth){EBox b;b.depth=depth;for(auto&v:b.lo)input>>v;for(auto&v:b.hi)input>>v;if(!input)throw std::runtime_error("truncated box");
  int old=alpha_exit(b);Found f=solve_box_fast(b);
  std::cout<<"{\"id\":\""<<id<<"\",\"depth\":"<<depth<<",\"old_alpha_code\":"<<old
   <<",\"closed_contradiction\":"<<(f.closed?"true":"false")<<",\"lp_height_approx\":";
  if(std::isfinite(f.height_lp))std::cout<<std::setprecision(17)<<f.height_lp;else std::cout<<"null";
  std::cout<<",\"height_t\":"<<f.height_t<<",\"margin\":\""<<f.height_margin<<"\",\"weights\":[";
  for(size_t i=0;i<f.w.size();i++){if(i)std::cout<<',';std::cout<<'['<<f.w[i].first<<','<<f.w[i].second<<']';}
  std::cout<<"]}"<<std::endl;
 }
}catch(const std::exception&e){std::cerr<<e.what()<<std::endl;return 1;}}
