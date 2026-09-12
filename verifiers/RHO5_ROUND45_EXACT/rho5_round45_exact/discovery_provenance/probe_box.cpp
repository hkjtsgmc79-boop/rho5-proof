#define main imported_v33_discovery_main
#include "discover.cpp"
#undef main
int main(){try{
 int count;if(!(std::cin>>count))return 1;
 std::cout<<std::setprecision(17);
 while(count--){std::string label;EBox b;std::cin>>label>>b.depth;
  for(int j=0;j<EV;j++)std::cin>>b.lo[j]>>b.hi[j];
  int code=rankone_exclusion(b);Found f=solve_box(b);
  std::cout<<"{\"label\":\""<<label<<"\",\"rank_code\":"<<code<<",\"integer_dual_closed\":"<<(f.closed?"true":"false")<<",\"values\":[";
  for(size_t j=0;j<f.val.size();j++){if(j)std::cout<<',';std::cout<<f.val[j];}
  std::cout<<"]}"<<std::endl;
 }
}catch(const std::exception&e){std::cerr<<e.what();return 1;}}
