#include "weighted_height.hpp"
#include <iostream>
#include <string>
int main(){try{std::string id;while(std::cin>>id){EBox b;for(auto&v:b.lo)std::cin>>v;for(auto&v:b.hi)std::cin>>v;long long t;int n;std::cin>>t>>n;std::vector<std::pair<int,long long>>w;for(int k=0;k<n;k++){int r;long long v;std::cin>>r>>v;w.push_back({r,v});}if(!std::cin)throw std::runtime_error("truncated");std::cout<<id<<' '<<weighted_height_margin(b,w,t)<<'\n';}}catch(const std::exception&e){std::cerr<<e.what();return 1;}}
