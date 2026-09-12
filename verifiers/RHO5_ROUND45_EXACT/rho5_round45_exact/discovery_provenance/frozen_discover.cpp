#include "mc_model.hpp"
#include "mc_simplex_dual.hpp"
#include "mc_exact_kernel.hpp"
#include "rankone_oracle.hpp"
#include <fstream>
#include <iostream>
#include <chrono>
#include <iomanip>
#include <cmath>
using Weights=std::vector<std::pair<int,long long>>;
const double US=UNIT.convert_to<double>();
struct Found{bool closed=false;Weights w;std::vector<double> val;};
Found solve_box(const EBox &nd){
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
 Simplex lp(A,b,obj);std::vector<double>x;double ans=lp.solve(x);Found out;
 if(std::isfinite(ans)&&x.size()==NX){out.val.resize(NX);for(int j=0;j<NX;j++)out.val[j]=lo[j]+x[j]*dd[j];}
 else{
  auto ww=lp.dual();double mx=0;std::vector<double>raw(scales.size());
  for(size_t i=0;i<raw.size();i++){raw[i]=std::max(0.,ww[i])/scales[i];mx=std::max(mx,raw[i]);}
  if(mx>0&&std::isfinite(mx))for(double prec:{1e6,1e9,1e12,1e15}){
   Weights w;for(size_t i=0;i<raw.size();i++)if(raw[i]>0){long long wi=std::llround(prec*raw[i]/mx);if(wi>0)w.push_back({i,wi});}
   if(!w.empty()&&contradiction_margin(nd,w)<0){out.closed=true;out.w=std::move(w);break;}
  }
 }
 return out;
}

long long new_nodes=0,leaves=0,opens=0,splits=0,old_leaves=0,solves=0;int maxdepth=0;
std::chrono::steady_clock::time_point start;double budget=60;long long max_solves=5000;
double elapsed(){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();}
void emit_leaf(std::ostream&out,const Weights&w){out<<"C "<<w.size();for(auto[i,v]:w)out<<' '<<i<<' '<<v;out<<'\n';leaves++;}
void refine(const EBox&box,std::ostream&out){
 if(elapsed()>=budget || solves>=max_solves || box.depth>=120){out<<"O\n";opens++;return;}
 new_nodes++;maxdepth=std::max(maxdepth,box.depth);
 int rank_code=rankone_exclusion(box);if(rank_code>=0){out<<"R "<<rank_code<<'\n';leaves++;return;}
 Found f=solve_box(box);solves++;
 if(solves%1000==0){out.flush();std::cout<<"solves="<<solves<<" new_leaves="<<leaves<<" depth="<<maxdepth<<" seconds="<<elapsed()<<std::endl;}
 if(f.closed){emit_leaf(out,f.w);return;}
 std::vector<double>score(NV);
 if(f.val.size()==NX)for(size_t n=0;n<pairs.size();n++){auto[i,j]=pairs[n];double err=std::abs(f.val[NV+n]-f.val[i]*f.val[j]);score[i]+=err;score[j]+=err;}
 double ss=0;for(int j=0;j<NV;j++){
 double den=(Big(eroothi[j]-erootlo[j])<<128).convert_to<double>();
 double rel=den>0?(box.hi[j]-box.lo[j]).convert_to<double>()/den:0;
 score[j]*=rel;ss+=score[j];}
 if(ss<1e-20)for(int j=0;j<NV;j++){double den=(Big(eroothi[j]-erootlo[j])<<128).convert_to<double>();score[j]=den>0?(box.hi[j]-box.lo[j]).convert_to<double>()/den:0;}
 int j=std::max_element(score.begin(),score.end())-score.begin();
 if(score[j]<=0){out<<"O\n";opens++;return;}
 out<<"S "<<j<<'\n';splits++;auto[l,h]=split_box(box,j);refine(l,out);refine(h,out);
}
void resume_tree(const EBox&box,std::istream&in,std::ostream&out){
 std::string op;if(!(in>>op))throw std::runtime_error("truncated checkpoint");
 if(op=="S"){int j;if(!(in>>j))throw std::runtime_error("bad split");out<<"S "<<j<<'\n';auto[l,h]=split_box(box,j);resume_tree(l,in,out);resume_tree(h,in,out);}
 else if(op=="C"){
 int n;if(!(in>>n)||n<1||n>EB+4*(int)pairs.size())throw std::runtime_error("bad old leaf");
 out<<"C "<<n;for(int i=0;i<n;i++){int j;long long w;if(!(in>>j>>w))throw std::runtime_error("truncated old weight");out<<' '<<j<<' '<<w;}out<<'\n';old_leaves++;
 }else if(op=="R"){int layer;if(!(in>>layer)||layer<0||layer>3)throw std::runtime_error("bad old rank leaf");out<<"R "<<layer<<'\n';old_leaves++;
 }else if(op=="O")refine(box,out);else throw std::runtime_error("unknown checkpoint tag");
}
int main(int argc,char**argv){try{
 if(argc<3||argc>5)throw std::runtime_error("usage: discover CHECKPOINT OUTPUT [SECONDS] [MAX_SOLVES]");
 if(argc>=4)budget=std::stod(argv[3]);if(argc==5)max_solves=std::stoll(argv[4]);
 std::ifstream in(argv[1]);std::ofstream out(argv[2]);if(!in||!out)throw std::runtime_error("open failed");
 start=std::chrono::steady_clock::now();resume_tree(root_box(),in,out);std::string junk;if(in>>junk)throw std::runtime_error("unused checkpoint tail");out.flush();if(!out)throw std::runtime_error("write failed");
 std::cout<<"{\"status\":\""<<(opens==0?"COMPLETE_CANDIDATE":"PARTIAL_CHECKPOINT")<<"\",\"new_nodes\":"<<new_nodes<<",\"new_leaves\":"<<leaves<<",\"old_leaves\":"<<old_leaves<<",\"open\":"<<opens<<",\"depth\":"<<maxdepth<<",\"seconds\":"<<elapsed()<<"}"<<std::endl;
 }catch(const std::exception&e){std::cerr<<"FAIL "<<e.what()<<std::endl;return 1;}}
