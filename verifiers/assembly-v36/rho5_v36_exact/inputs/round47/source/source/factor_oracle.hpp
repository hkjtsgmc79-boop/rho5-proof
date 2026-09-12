#pragma once
#include "factor_graph.hpp"
// The positional dictionary is audited by the Python source checker. HEAD_TYPE
// explicitly binds G=e*beta (1) or G=e*u0 (2) to the frozen model.
inline int make_factor_packets(const EBox&b,std::vector<Packet>&packets){
 static_assert(EV==23,"expected 22 native coordinates and actual G");
 static_assert(HEAD_TYPE==1||HEAD_TYPE==2,"invalid head type");
 if(b.lo[0]<=0||b.lo[7]<=0)throw std::runtime_error("positive p,k required");
 const BI one{-UNIT2,UNIT2},zero{Big(0),Big(0)},pb{-b.hi[7]*UNIT,b.hi[7]*UNIT},kb{-b.hi[0]*UNIT,b.hi[0]*UNIT};
 Packet C,X,Y;
 C.a={var_i(b,5),var_i(b,6)};C.b={var_i(b,0),var_i(b,3),var_i(b,4)};
 C.z.resize(2,std::vector<BI>(3));int corej[3]={0,3,4};
 for(int i=0;i<2;i++)for(int j=0;j<3;j++)C.z[i][j]=raw_product_i(b,5+i,corej[j]);
 X.a={{UNIT2,UNIT2},var_i(b,13),var_i(b,14),var_i(b,15)};
 X.b={var_i(b,7),var_i(b,19),var_i(b,20),var_i(b,21)};X.z.resize(4,std::vector<BI>(4));
 int stagej[4]={7,19,20,21};for(int j=0;j<4;j++)X.z[0][j]=var_i(b,stagej[j]);
 for(int i=0;i<3;i++)for(int j=0;j<4;j++)X.z[i+1][j]=raw_product_i(b,13+i,stagej[j]);
 Y.a={var_i(b,9),var_i(b,10),var_i(b,11),var_i(b,12)};Y.b={var_i(b,8),var_i(b,16),var_i(b,17),var_i(b,18)};Y.z.resize(4,std::vector<BI>(4));
 int orig_i[4]={9,10,11,12},orig_j[4]={8,16,17,18};
 for(int i=0;i<4;i++)for(int j=0;j<4;j++)Y.z[i][j]=raw_product_i(b,orig_i[i],orig_j[j]);
 Y.z[0][0]=meet_i(Y.z[0][0],minus_i(var_i(b,7),one));
 int gi=HEAD_TYPE==1?0:1;Y.z[gi][0]=meet_i(Y.z[gi][0],var_i(b,22));
 std::array<std::array<BI,3>,3>D,S,O;
 for(int j=0;j<3;j++)D[0][j]=var_i(b,corej[j]);
 for(int i=1;i<3;i++)for(int j=0;j<3;j++)D[i][j]=plus_i(C.z[i-1][j],j==0?zero:var_i(b,(i==2&&j==2)?2:1));
 for(int i=0;i<3;i++)for(int j=0;j<3;j++){S[i][j]=pb;O[i][j]=one;}
 for(int pass=0;pass<3;pass++){
  for(int i=0;i<3;i++){
   Y.z[i+1][0]=meet_i(Y.z[i+1][0],minus_i(X.z[i+1][0],one));
   X.z[i+1][0]=meet_i(X.z[i+1][0],plus_i(Y.z[i+1][0],one));
   Y.z[0][i+1]=meet_i(Y.z[0][i+1],minus_i(one,var_i(b,19+i)));
   for(int j=0;j<3;j++){
    D[i][j]=meet_i(D[i][j],kb);
    S[i][j]=meet_i(S[i][j],meet_i(plus_i(D[i][j],X.z[i+1][j+1]),pb));
    O[i][j]=meet_i(O[i][j],plus_i(S[i][j],Y.z[i+1][j+1]));
    if(empty_i(D[i][j])||empty_i(S[i][j])||empty_i(O[i][j])||empty_i(X.z[i+1][j+1])||empty_i(Y.z[i+1][j+1]))return 3;
    Y.z[i+1][j+1]=meet_i(Y.z[i+1][j+1],minus_i(O[i][j],S[i][j]));
    S[i][j]=meet_i(S[i][j],minus_i(O[i][j],Y.z[i+1][j+1]));
    X.z[i+1][j+1]=meet_i(X.z[i+1][j+1],minus_i(S[i][j],D[i][j]));
    D[i][j]=meet_i(D[i][j],minus_i(S[i][j],X.z[i+1][j+1]));
    if(i){const BI H=j==0?zero:var_i(b,(i==2&&j==2)?2:1);C.z[i-1][j]=meet_i(C.z[i-1][j],minus_i(D[i][j],H));D[i][j]=meet_i(D[i][j],plus_i(C.z[i-1][j],H));}
   }
  }
  for(const auto*ptr:{&C,&X,&Y})for(const auto&row:ptr->z)for(const auto&v:row)if(empty_i(v))return 3;
  for(int i=0;i<3;i++)for(int j=0;j<3;j++)if(empty_i(D[i][j])||empty_i(S[i][j])||empty_i(O[i][j]))return 3;
 }
 packets={X,Y,C};return -1;
}
inline int factor_exclusion(const EBox&box){
 std::vector<Packet>p;int code=make_factor_packets(box,p);if(code>=0)return code;
 for(int i=0;i<3;i++)if(!packet_feasible(p[i]))return i;
 return -1;
}
