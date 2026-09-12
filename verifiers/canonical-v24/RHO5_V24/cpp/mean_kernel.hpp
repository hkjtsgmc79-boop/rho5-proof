#pragma once
// Mean-value necessary enclosures. Derivative graph expressions are regenerated
// from the original polynomial system by exact symbolic differentiation.
static const std::vector<Node> core_spec(spec.begin(),spec.begin()+BASE_COUNT);
inline I eval_node(const Node& n,const std::vector<I>& z){
 if(n.op==1)return I(n.value,n.value);
 if(n.op==2)return plus(z[n.a],z[n.b]);
 if(n.op==3)return times(z[n.a],z[n.b]);
 throw std::runtime_error("invalid mean-value opcode");
}
inline bool mean_contract(Box& box){
 std::vector<I> range(spec.size()),center(BASE_COUNT);
 std::array<I,NV> disp,mid;
 for(int i=0;i<NV;i++){
  range[i]=box.x[i];Z m=box.x[i].l+(box.x[i].h-box.x[i].l)/2;
  mid[i]=I(m,m);center[i]=mid[i];disp[i]=minus(box.x[i],mid[i]);
 }
 for(std::size_t i=NV;i<spec.size();i++){
  range[i]=eval_node(spec[i],range);
  if(i<BASE_COUNT)center[i]=eval_node(spec[i],center);
 }
 for(std::size_t ri=0;ri<roots.size();ri++){
  I fmid=center[roots[ri].first];
  std::array<I,NV> term;
  std::array<I,NV+1> pre,suf;pre[0]=I(0,0);suf[NV]=I(0,0);
  for(int i=0;i<NV;i++){term[i]=times(range[gradrefs[ri][i]],disp[i]);pre[i+1]=plus(pre[i],term[i]);}
  for(int i=NV-1;i>=0;i--)suf[i]=plus(term[i],suf[i+1]);
  I total=plus(fmid,pre[NV]);I target=roots[ri].second?I(0,0):I(0,INF);
  if(!meet(total,target))return true;
  for(int i=0;i<NV;i++){
   I gi=range[gradrefs[ri][i]];
   if(gi.l<=0&&gi.h>=0)continue;
   I rest=plus(fmid,plus(pre[i],suf[i+1]));
   I candidate=plus(mid[i],divide(minus(target,rest),gi));
   if(!meet(box.x[i],candidate))return true;
  }
 }
 return false;
}
inline bool contract_all(Box& box){
 for(int round=0;round<3;round++){
  auto old=box.x;
  if(contract(box,core_spec,roots))return true;
  if(mean_contract(box))return true;
  bool changed=false;
  for(int i=0;i<NV;i++)if(box.x[i].l>old[i].l+SCALE/10000000||box.x[i].h<old[i].h-SCALE/10000000)changed=true;
  if(!changed)break;
 }
 return false;
}
