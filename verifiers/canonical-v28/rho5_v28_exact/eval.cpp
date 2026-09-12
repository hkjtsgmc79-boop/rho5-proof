#include "guards.hpp"
#include <cstdio>
extern "C" {
// Outputs 37 value intervals and 37 necessary affine rows (b,a0,...,a5).
// Rows 0..34 are unconditional; row 35 is enabled only if g36>=0.
int eval(const int64_t *lo,const int64_t *hi,int64_t fn,int64_t fd,int64_t *bounds,int64_t *rows){
 try{
  using namespace ex;
  std::array<D,6>x;std::array<I,6>c;std::array<i64,6>rad;
  for(int i=0;i<6;i++){if(lo[i]>hi[i])return -2;x[i]=D::var(i,I::raw(lo[i],hi[i]));i64 cc=checked(floordiv(i128(lo[i])+hi[i],2));c[i]=I::raw(cc,cc);rad[i]=std::max(cc-lo[i],hi[i]-cc);}
  auto g=guards(x,I::rat(fn,checked(i128(fd)*2)));auto gc=guards(c,I::rat(fn,checked(i128(fd)*2)));
  for(int j=0;j<37;j++){
   bounds[2*j]=g[j].v.lo;bounds[2*j+1]=g[j].v.hi;i64 b=gc[j].hi;
   for(int i=0;i<6;i++){
    auto a=g[j].d[i]*I::raw(rad[i],rad[i]);i64 mid=checked(floordiv(i128(a.lo)+a.hi,2));
    i64 err=std::max(mid-a.lo,a.hi-mid);b=checked(i128(b)+err);rows[7*j+i+1]=mid;
   }
   rows[7*j]=b;
  }
  return 0;
 }catch(const std::exception&e){fprintf(stderr,"EVAL ERROR %s\n",e.what());return -1;}
}
}
extern "C" int interval_arithmetic(int64_t al,int64_t ah,int64_t bl,int64_t bh,int op,int64_t*out){
 try{auto a=ex::I::raw(al,ah),b=ex::I::raw(bl,bh);ex::I z;
 if(op==0)z=a+b;else if(op==1)z=a-b;else if(op==2)z=a*b;else return -2;
 out[0]=z.lo;out[1]=z.hi;return 0;
 }catch(...){return -1;}
}
