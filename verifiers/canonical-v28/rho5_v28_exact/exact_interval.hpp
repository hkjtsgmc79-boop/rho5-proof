#pragma once
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <algorithm>
#include <array>
#include <cmath>

// Dyadic intervals, exact directed rounding on the 2^-40 grid.
// Every intermediate integer sum/product is checked before conversion.
namespace ex {
using i64=int64_t; using i128=__int128_t;
constexpr int P=40; constexpr i64 S=i64(1)<<P;
inline i64 checked(i128 x){if(x>std::numeric_limits<i64>::max()||x<std::numeric_limits<i64>::min())throw std::overflow_error("fixed interval overflow");return (i64)x;}
inline i128 floordiv(i128 x,i128 y){i128 q=x/y,r=x%y;if(r<0)--q;return q;}
inline i128 ceildiv(i128 x,i128 y){return -floordiv(-x,y);}
struct I{
 i64 lo,hi;
 I():lo(0),hi(0){} I(int n):lo(checked(i128(n)*S)),hi(lo){}
 static I raw(i64 l,i64 h){if(l>h)throw std::runtime_error("inverted interval");I x;x.lo=l;x.hi=h;return x;}
 static I rat(i64 n,i64 d){if(d<=0)throw std::runtime_error("denominator");return raw(checked(floordiv(i128(n)*S,d)),checked(ceildiv(i128(n)*S,d)));}
};
inline I operator+(I a,I b){return I::raw(checked(i128(a.lo)+b.lo),checked(i128(a.hi)+b.hi));}
inline I operator-(I a){return I::raw(checked(-i128(a.hi)),checked(-i128(a.lo)));}
inline I operator-(I a,I b){return a+(-b);}
inline I operator*(I a,I b){i128 p[]={i128(a.lo)*b.lo,i128(a.lo)*b.hi,i128(a.hi)*b.lo,i128(a.hi)*b.hi};return I::raw(checked(floordiv(*std::min_element(p,p+4),S)),checked(ceildiv(*std::max_element(p,p+4),S)));}
constexpr int N=6;
struct D{
 I v;std::array<I,N>d;
 D():v(0){} D(int n):v(n){} D(I x):v(x){}
 static D var(int j,I x){D a(x);a.d[j]=I(1);return a;}
};
inline D operator+(const D&a,const D&b){D c(a.v+b.v);for(int i=0;i<N;++i)c.d[i]=a.d[i]+b.d[i];return c;}
inline D operator-(const D&a){D c(-a.v);for(int i=0;i<N;++i)c.d[i]=-a.d[i];return c;}
inline D operator-(const D&a,const D&b){return a+(-b);}
inline D operator*(const D&a,const D&b){D c(a.v*b.v);for(int i=0;i<N;++i)c.d[i]=a.d[i]*b.v+a.v*b.d[i];return c;}
}
