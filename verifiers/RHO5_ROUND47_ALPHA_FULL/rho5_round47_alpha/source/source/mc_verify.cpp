// Standalone exact acceptance. No simplex, no floating point, no optimizer.
#include "mc_exact_kernel.hpp"
#include "rankone_oracle.hpp"
#include "factor_oracle.hpp"
#include "alpha_ports.hpp"
#include "weighted_height.hpp"
#include <fstream>
#include <iostream>
#include <chrono>
#include <sstream>
#include <climits>
std::array<long long,4>packet_counts{};long long rank_leaves=0;long long factor_leaves=0;std::array<long long,4>factor_counts{};bool allow_open=false;long long safe_leaves=0;long long weighted_safe_leaves=0;std::array<long long,11>safe_counts{};long long opens=0;long long nodes=0,leaves=0,splits=0,total_support=0;int maxdepth=0,maxsupport=0;
void v33_visit_node(const EBox&box,std::istream&in){
 if(++nodes>50000000||box.depth>512)throw std::runtime_error("certificate size/depth limit");
 maxdepth=std::max(maxdepth,box.depth);std::string tag;if(!(in>>tag))throw std::runtime_error("truncated tree");
 if(tag=="S"){
  int j;if(!(in>>j))throw std::runtime_error("invalid split value");auto[l,h]=split_box(box,j);splits++;v33_visit_node(l,in);v33_visit_node(h,in);
 }else if(tag=="C"){
  int n;if(!(in>>n)||n<1||n>EB+4*(int)epairs.size())throw std::runtime_error("bad support count");
  std::vector<std::pair<int,long long>>weights;for(int t=0;t<n;t++){int j;long long w;if(!(in>>j>>w))throw std::runtime_error("truncated/out-of-range weight");weights.emplace_back(j,w);}
  Big margin=contradiction_margin(box,weights);if(margin>=0)throw std::runtime_error("leaf is NOT a strict contradiction at leaf "+std::to_string(leaves));
  leaves++;total_support+=n;maxsupport=std::max(maxsupport,n);
 }else if(tag=="H"){
  long long objective_weight;int n;
  if(!(in>>objective_weight>>n)||objective_weight<=0||n<1||n>EB+4*(int)epairs.size())throw std::runtime_error("bad height support count/objective weight");
  std::vector<std::pair<int,long long>>weights;
  for(int i=0;i<n;i++){int row;long long w;if(!(in>>row>>w))throw std::runtime_error("truncated/out-of-range height weight");weights.emplace_back(row,w);}
  if(weighted_height_margin(box,weights,objective_weight)>0)throw std::runtime_error("height leaf does NOT bound F by alpha");
  leaves++;safe_leaves++;weighted_safe_leaves++;total_support+=n;maxsupport=std::max(maxsupport,n);
 }else if(tag=="R"){
  int layer;if(!(in>>layer)||layer<0||layer>3)throw std::runtime_error("invalid rank-one layer");
  if(rankone_exclusion(box)!=layer)throw std::runtime_error("rank-one interval certificate does not exclude this box");
  leaves++;rank_leaves++;packet_counts[layer]++;
 }else if(tag=="P"){
  int layer;if(!(in>>layer)||layer<0||layer>3)throw std::runtime_error("invalid full-factor layer");
  if(factor_exclusion(box)!=layer)throw std::runtime_error("bounded factor feasibility does not exclude this box");
  leaves++;factor_leaves++;factor_counts[layer]++;
 }else if(tag=="A"){
  int code;if(!(in>>code)||code<0||code>10)throw std::runtime_error("invalid alpha-safe exit code");
  if(!alpha_exit_proves(box,code))throw std::runtime_error("box NOT certified by claimed alpha-safe exit");
  leaves++;safe_leaves++;safe_counts[code]++;
 }else if(tag=="O" && allow_open){opens++;}else throw std::runtime_error("unknown/unpaid instruction: "+tag);
}
int main(int argc,char**argv){try{
 if(argc<2||argc>3)throw std::runtime_error("usage: mc_verify TREE [--allow-open]");if(argc==3){if(std::string(argv[2])!="--allow-open")throw std::runtime_error("invalid flag");allow_open=true;}
 std::ifstream in(argv[1]);if(!in)throw std::runtime_error("file open failed");auto start=std::chrono::steady_clock::now();
 v33_visit_node(root_box(),in);std::string unused;if(in>>unused)throw std::runtime_error("trailing unvisited records");
 if(nodes!=2*splits+1||leaves+opens!=splits+1)throw std::runtime_error("partition bookkeeping mismatch");
 auto seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
 std::cout<<"{\"status\":\""<<(opens?"V35_PARTIAL_ALPHA_LOCALIZATION_CHECKPOINT":"V35_ORIGINAL_ROOT_ALPHA_LOCALIZATION_PASS")<<"\",\"nodes\":"<<nodes<<",\"splits\":"<<splits<<",\"leaves\":"<<leaves<<",\"packet_interval_leaves\":"<<rank_leaves<<",\"determinant_interval_leaves\":"<<(packet_counts[0]+packet_counts[1]+packet_counts[2])<<",\"direct_packet_interval_leaves\":"<<packet_counts[3]<<",\"full_factor_leaves\":"<<factor_leaves<<",\"factor_graph_leaves\":"<<(factor_counts[0]+factor_counts[1]+factor_counts[2])<<",\"factor_direct_leaves\":"<<factor_counts[3]<<",\"contradiction_leaves\":"<<(leaves-safe_leaves)<<",\"alpha_safe_leaves\":"<<safe_leaves<<",\"weighted_height_leaves\":"<<weighted_safe_leaves<<",\"local_flow_leaves\":"<<(safe_counts[0]+safe_counts[1]+safe_counts[2]+safe_counts[3]+safe_counts[7]+safe_counts[8]+safe_counts[9]+safe_counts[10])<<",\"R0_leaves\":"<<safe_counts[4]<<",\"tail_bound_leaves\":"<<safe_counts[5]<<",\"direct_height_leaves\":"<<safe_counts[6]<<",\"flow_tube_leaves\":"<<(safe_counts[7]+safe_counts[8]+safe_counts[9]+safe_counts[10])<<",\"open\":"<<opens<<",\"max_depth\":"<<maxdepth<<",\"max_support\":"<<maxsupport<<",\"total_support\":"<<total_support<<",\"seconds\":"<<seconds<<"}"<<std::endl;
 }catch(const std::exception&e){std::cerr<<"REJECTED: "<<e.what()<<std::endl;return 1;}}
