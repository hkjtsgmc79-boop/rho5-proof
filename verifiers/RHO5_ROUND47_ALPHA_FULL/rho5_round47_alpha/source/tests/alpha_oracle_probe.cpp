#include "alpha_ports.hpp"
#include <iostream>
int main(){try{int count;if(!(std::cin>>count)||count<0||count>10000)return 2;for(int t=0;t<count;t++){EBox b;for(int i=0;i<EV;i++){if(!(std::cin>>b.lo[i]>>b.hi[i])||b.lo[i]>b.hi[i])return 3;}for(int c=0;c<11;c++)std::cout<<(alpha_exit_proves(b,c)?1:0)<<' ';std::cout<<'\n';}}catch(const std::exception&e){std::cerr<<e.what();return 4;}}
