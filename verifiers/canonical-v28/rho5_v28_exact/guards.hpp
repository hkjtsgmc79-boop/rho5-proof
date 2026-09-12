#pragma once
#include "exact_interval.hpp"
template<class Num> std::array<Num,37> guards(const std::array<Num,6>&x,ex::I rr){
 auto beta=x[0], V=x[1], ss=x[2], Y=x[3], Z=x[4], v=x[5];
 Num r(rr);
 auto R=r-1;
 auto eps=R-1;
 auto p=1+ss;
 auto T=p*Z-1;
 auto q=1-beta*v;
 auto gamma=V-beta*Y;
 auto nu=beta*Z-T;
 auto mu=V*Z-T*Y;
 auto A=R+Y+gamma*v;
 auto C=R-Z+nu*v;
 auto W=R*(Y+Z)+mu*v;
 auto N=V*(Y+Z)+ss*mu;
 auto Dh=mu+R*(nu-gamma);
 auto nh=A*(R-Z)+C*(R-Y);
 auto B0=2+(1-beta)*v;
 auto fraka=R*(1+q)+V*v;
 auto frakc=V+beta*R;
 auto u0=r*A+C*(R-Y);
 auto u1=C*gamma;
 auto d1=1-V-beta*eps;
 auto ah=eps*(1+q)-(1-V)*v;
 auto dS=V+beta*(eps-v);
 auto sh=p*q+1+v-fraka;
 auto Bs=B0+(1+beta)*ss;
 auto Ds=fraka+frakc*ss;
 auto c0=N*A*A*B0-V*W*u0*fraka;
 auto c1=N*A*A*(1+beta)-V*W*(u0*frakc+u1*fraka);
 auto c2=-V*W*u1*frakc;
 auto vw_j=N*q-(V+T)*(ss*R-V*v);
 auto Pguard=V*W-vw_j-beta*ss*W;
 return {beta-ss,T,nu,gamma,mu,ss-v,V-ss,B0-A,
        (ss-V*v)*mu-eps*V*(Y+Z),d1,(1-V)*(ss+v)-eps*(2+beta*(ss-v)),Dh,
        beta*ss-ss*ss-eps*beta,3-2*R-beta,(1+beta)*Y-V,1-p*Y+V,
        ss*Dh-beta*nh,sh*Dh-nh*dS,N*A*B0*Dh-V*W*(u0*Dh+u1*nh),
        N*A*B0*d1-V*W*(u0*d1+u1*ah),Pguard,vw_j,
        p*q*V*W-N*q*A+vw_j*(A-1-v),q*Y+V*(1+v)-V*A,
        N*A*A*Bs*Dh-V*W*Ds*(u0*Dh+u1*nh),A*Bs-(1+v)*Ds,
        c1*c1-4*c0*c2,9*V*W-4*N*A,(9*A-4*u0)*Dh-4*u1*nh,
        (1-T)*V*W-C*N,(3-r)*V-ss,17*q-16*R-16*V*v+16*v*(1+beta),
        B0*(R+V*v)-A*(1+v),(R+V*v-q)*B0+A*(p*q-1-v),gamma-nu,c0+c1*ss+c2*ss*ss,c1+2*c2*ss};
}