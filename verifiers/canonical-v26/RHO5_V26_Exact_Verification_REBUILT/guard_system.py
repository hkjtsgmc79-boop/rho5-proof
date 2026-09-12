"""Exact V26 f_minus localization guards reconstructed from REPORT.md."""
import sympy as s

beta,V,ss,Y,Z,v=s.symbols("beta V s Y Z v")
variables=(beta,V,ss,Y,Z,v)
f=s.Rational(4132517,10**6)
r=f/2
R=r-1
eps=R-1
p=1+ss
T=p*Z-1
q=1-beta*v
gamma=V-beta*Y
nu=beta*Z-T
mu=V*Z-T*Y
A=R+Y+gamma*v
C=R-Z+nu*v
W=R*(Y+Z)+mu*v
N=V*(Y+Z)+ss*mu
Dh=mu+R*(nu-gamma)
nh=A*(R-Z)+C*(R-Y)
B0=2+(1-beta)*v
fraka=R*(1+q)+V*v
frakc=V+beta*R
u0=r*A+C*(R-Y)
u1=C*gamma
d1=1-V-beta*eps
ah=eps*(1+q)-(1-V)*v
dS=V+beta*(eps-v)
sh=p*q+1+v-fraka
Bs=B0+(1+beta)*ss
Ds=fraka+frakc*ss
c0=N*A**2*B0-V*W*u0*fraka
c1=N*A**2*(1+beta)-V*W*(u0*frakc+u1*fraka)
c2=-V*W*u1*frakc
vw_j=N*q-(V+T)*(ss*R-V*v)
Pguard=V*W-vw_j-beta*ss*W

guards=[
 beta-ss, T, nu, gamma, mu, ss-v, V-ss,
 B0-A,
 (ss-V*v)*mu-eps*V*(Y+Z),
 d1,
 (1-V)*(ss+v)-eps*(2+beta*(ss-v)),
 Dh,
 beta*ss-ss**2-eps*beta,
 3-2*R-beta,
 (1+beta)*Y-V,
 1-p*Y+V,
 ss*Dh-beta*nh,
 sh*Dh-nh*dS,
 N*A*B0*Dh-V*W*(u0*Dh+u1*nh),
 N*A*B0*d1-V*W*(u0*d1+u1*ah),
 Pguard,
 vw_j,
 p*q*V*W-N*q*A+vw_j*(A-1-v),
 q*Y+V*(1+v)-V*A,
 N*A**2*Bs*Dh-V*W*Ds*(u0*Dh+u1*nh),
 A*Bs-(1+v)*Ds,
 c1**2-4*c0*c2,
 9*V*W-4*N*A,
 (9*A-4*u0)*Dh-4*u1*nh,
 (1-T)*V*W-C*N,
 (3-r)*V-ss,
 17*q-16*R-16*V*v+16*v*(1+beta),
 B0*(R+V*v)-A*(1+v),
 (R+V*v-q)*B0+A*(p*q-1-v),
 gamma-nu,
]
g35=c0+c1*ss+c2*ss**2
g36=c1+2*c2*ss
assert len(guards)==35
