#include "second_interval.hpp"
#include "guards.hpp"
#include <cstdio>
extern "C" int eval_taylor(const int64_t*lo,const int64_t*hi,int64_t fn,int64_t fd,int64_t*bounds,int64_t*rows){
 try{
 using namespace ex;
 std::array<D2,6>x;std::array<D,6>c;std::array<i64,6>rad;
 for(int i=0;i<6;i++){x[i]=D2::var(i,I::raw(lo[i],hi[i]));i64 cc=checked(floordiv(i128(lo[i])+hi[i],2));c[i]=D::var(i,I::raw(cc,cc));rad[i]=std::max(cc-lo[i],hi[i]-cc);}
 auto g=guards(x,I::rat(fn,checked(i128(fd)*2)));auto gc=guards(c,I::rat(fn,checked(i128(fd)*2)));
 for(int j=0;j<37;j++){
  bounds[2*j]=g[j].v.lo;bounds[2*j+1]=g[j].v.hi;i64 b=gc[j].v.hi;I rem(0);
  for(int i=0;i<6;i++){
   I ri=I::raw(rad[i],rad[i]);auto a=gc[j].d[i]*ri;i64 mid=checked(floordiv(i128(a.lo)+a.hi,2));b=checked(i128(b)+std::max(mid-a.lo,a.hi-mid));rows[7*j+i+1]=mid;
   rem=rem+I::rat(1,2)*I::raw(0,std::max(i64(0),g[j].h[i][i].hi))*ri*ri;
   for(int k=0;k<i;k++){
    auto z=g[j].h[i][k];i64 mx=std::max(checked(-i128(z.lo)),z.hi);
    rem=rem+I::raw(0,mx)*ri*I::raw(rad[k],rad[k]);
   }
  }
  rows[7*j]=checked(i128(b)+rem.hi);
 }
 return 0;
 }catch(const std::exception&e){fprintf(stderr,"TAYLOR ERROR %s\n",e.what());return -1;}
}
