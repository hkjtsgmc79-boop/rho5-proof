#pragma once
#include "exact_interval.hpp"
namespace ex {
struct D2{
 I v;std::array<I,6>d;std::array<std::array<I,6>,6>h;
 D2():v(0){} D2(int n):v(n){} D2(I x):v(x){}
 static D2 var(int j,I x){D2 a(x);a.d[j]=I(1);return a;}
};
inline D2 operator+(const D2&a,const D2&b){D2 c(a.v+b.v);for(int i=0;i<6;i++){c.d[i]=a.d[i]+b.d[i];for(int j=0;j<6;j++)c.h[i][j]=a.h[i][j]+b.h[i][j];}return c;}
inline D2 operator-(const D2&a){D2 c(-a.v);for(int i=0;i<6;i++){c.d[i]=-a.d[i];for(int j=0;j<6;j++)c.h[i][j]=-a.h[i][j];}return c;}
inline D2 operator-(const D2&a,const D2&b){return a+(-b);}
inline D2 operator*(const D2&a,const D2&b){D2 c(a.v*b.v);for(int i=0;i<6;i++){c.d[i]=a.d[i]*b.v+a.v*b.d[i];for(int j=0;j<6;j++)c.h[i][j]=a.h[i][j]*b.v+a.d[i]*b.d[j]+a.d[j]*b.d[i]+a.v*b.h[i][j];}return c;}
}
