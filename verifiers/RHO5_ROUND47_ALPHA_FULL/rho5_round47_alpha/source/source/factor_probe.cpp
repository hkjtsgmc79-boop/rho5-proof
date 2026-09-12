#include "factor_oracle.hpp"
#include <iostream>
#include <string>
#include <chrono>
int main(int argc,char**argv){try{
 if(argc!=2)throw std::runtime_error("probe box|packet");std::string mode=argv[1];
 if(mode=="packet"){
  int m,n;while(std::cin>>m>>n){if(m<0||m>8||n<0||n>8)throw std::runtime_error("dimensions");Packet p;
   p.a.resize(m);p.b.resize(n);p.z.resize(m,std::vector<BI>(n));
   for(auto&v:p.a)if(!(std::cin>>v.lo>>v.hi))throw std::runtime_error("truncated");
   for(auto&v:p.b)if(!(std::cin>>v.lo>>v.hi))throw std::runtime_error("truncated");
   for(auto&r:p.z)for(auto&v:r)if(!(std::cin>>v.lo>>v.hi))throw std::runtime_error("truncated");
   std::cout<<(packet_feasible(p)?1:0)<<std::endl;
  }
 }else if(mode=="box"){
  std::string sentinel;while(std::cin>>sentinel){if(sentinel!="B")throw std::runtime_error("bad sentinel");EBox b;
   for(int i=0;i<EV;i++)if(!(std::cin>>b.lo[i]>>b.hi[i]))throw std::runtime_error("truncated box");
   auto t=std::chrono::steady_clock::now();int old=rankone_exclusion(b),now=factor_exclusion(b);double dt=std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count();
   std::cout<<old<<' '<<now<<' '<<dt<<std::endl;
  }
 }else throw std::runtime_error("bad mode");
}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
