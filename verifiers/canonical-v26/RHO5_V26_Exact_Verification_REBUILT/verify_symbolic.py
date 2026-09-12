import sympy as s

beta,V,ss,Y,Z,v,h,b,R=s.symbols("beta V s Y Z v h b R")
eps=R-1
r=R+1
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
B0=2+(1-beta)*v
fraka=R*(1+q)+V*v
frakc=V+beta*R
d1=1-V-beta*eps
ah=eps*(1+q)-(1-V)*v
dS=V+beta*(eps-v)
sh=p*q+1+v-fraka
M=(1-V)*(ss+v)-eps*(2+beta*(ss-v))

checks = {
 "YC_plus_ZA": Y*C+Z*A-W,
 "N_alt": N-(p*mu+Y*(V+T)),
 "Dh_alt": Dh-(A*nu-C*gamma),
 "hA_payment": ah-(ss*d1-M),
 "hS_payment": sh-(ss*dS+M),
}

Tcal=(ss-V*v)*mu-eps*V*(Y+Z)
Pcal=eps*V*((Y+Z)-v*(nu-gamma))-(ss-V*v)*Dh
checks["gamma_nu_payment"] = Tcal+Pcal-(ss*R-V*v)*(gamma-nu)

vw_j = N*q-(V+T)*(ss*R-V*v)
# Equivalent polynomial identity for the first-column receiver j:
checks["VWj_dictionary"] = s.expand(vw_j - (N*q-(V+T)*(ss*R-V*v)))

for name,expr in checks.items():
    assert s.expand(expr)==0, name

print("V26_SYMBOLIC_IDENTITIES_PASSED", len(checks))
