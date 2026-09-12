// Standalone exact acceptance. No simplex, no floating point, no optimizer.
#include "mc_exact_kernel.hpp"
#include <fstream>
#include <iostream>
#include <chrono>
#include <sstream>
#include <climits>
long long nodes=0,leaves=0,splits=0,total_support=0;int maxdepth=0,maxsupport=0;
void visit(const EBox&box,std::istream&in){
 if(++nodes>4000000||box.depth>180)throw std::runtime_error("certificate size/depth limit");
 maxdepth=std::max(maxdepth,box.depth);std::string tag;if(!(in>>tag))throw std::runtime_error("truncated tree");
 if(tag=="S"){
  int j;if(!(in>>j))throw std::runtime_error("invalid split value");auto[l,h]=split_box(box,j);splits++;visit(l,in);visit(h,in);
 }else if(tag=="C"){
  int n;if(!(in>>n)||n<1||n>EB+4*(int)epairs.size())throw std::runtime_error("bad support count");
  std::vector<std::pair<int,long long>>weights;for(int t=0;t<n;t++){int j;long long w;if(!(in>>j>>w))throw std::runtime_error("truncated/out-of-range weight");weights.emplace_back(j,w);}
  Big margin=contradiction_margin(box,weights);if(margin>=0)throw std::runtime_error("leaf is NOT a strict contradiction at leaf "+std::to_string(leaves));
  leaves++;total_support+=n;maxsupport=std::max(maxsupport,n);
 }else throw std::runtime_error("unknown/unpaid instruction: "+tag);
}
int main(int argc,char**argv){try{
 if(argc!=2)throw std::runtime_error("usage: mc_verify EXACT_TREE");
 std::ifstream in(argv[1]);if(!in)throw std::runtime_error("file open failed");auto start=std::chrono::steady_clock::now();
 visit(root_box(),in);std::string unused;if(in>>unused)throw std::runtime_error("trailing unvisited records");
 if(nodes!=2*splits+1||leaves!=splits+1)throw std::runtime_error("partition bookkeeping mismatch");
 auto seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
 std::cout<<"{\"status\":\"V31_SMALL_PIVOT_GLOBAL_EXACT_PASS\",\"nodes\":"<<nodes<<",\"splits\":"<<splits<<",\"leaves\":"<<leaves<<",\"open\":0,\"max_depth\":"<<maxdepth<<",\"max_support\":"<<maxsupport<<",\"total_support\":"<<total_support<<",\"seconds\":"<<seconds<<"}"<<std::endl;
 }catch(const std::exception&e){std::cerr<<"REJECTED: "<<e.what()<<std::endl;return 1;}}
