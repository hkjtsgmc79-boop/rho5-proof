from fractions import Fraction as Q
NV=6
class I:
    __slots__=('lo','hi')
    def __init__(self,lo,hi=None):
        self.lo=lo; self.hi=lo if hi is None else hi
        if self.lo>self.hi: raise ValueError((self.lo,self.hi))
    def __add__(self,o): o=toI(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,o): return self+(-toI(o))
    def __rsub__(self,o): return toI(o)-self
    def __mul__(self,o):
        o=toI(o); z=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi); return I(min(z),max(z))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=toI(o)
        if o.lo<=0<=o.hi: raise ZeroDivisionError((o.lo,o.hi))
        z=(Q(1,1)/o.lo,Q(1,1)/o.hi); return self*I(min(z),max(z))
    def __rtruediv__(self,o): return toI(o)/self

def toI(x): return x if isinstance(x,I) else I(x)

class D:
    __slots__=('v','d')
    def __init__(self,v,d=None):
        self.v=toI(v); self.d=[I(Q(0)) for _ in range(NV)] if d is None else d
    @classmethod
    def var(cls,i,lo,hi):
        d=[I(Q(0)) for _ in range(NV)]; d[i]=I(Q(1)); return cls(I(lo,hi),d)
    def __add__(self,o): o=toD(o); return D(self.v+o.v,[self.d[i]+o.d[i] for i in range(NV)])
    __radd__=__add__
    def __neg__(self): return D(-self.v,[-x for x in self.d])
    def __sub__(self,o): return self+(-toD(o))
    def __rsub__(self,o): return toD(o)-self
    def __mul__(self,o):
        o=toD(o); return D(self.v*o.v,[self.d[i]*o.v+self.v*o.d[i] for i in range(NV)])
    __rmul__=__mul__
    def __truediv__(self,o):
        o=toD(o); den=o.v*o.v
        return D(self.v/o.v,[(self.d[i]*o.v-self.v*o.d[i])/den for i in range(NV)])
    def __rtruediv__(self,o): return toD(o)/self

def toD(x): return x if isinstance(x,D) else D(x)

def guards_generic(x,f):
    beta,V,ss,Y,Z,v=x
    r=f/2; R=r-1; eps=R-1; p=1+ss; T=p*Z-1; q=1-beta*v
    gamma=V-beta*Y;nu=beta*Z-T;mu=V*Z-T*Y
    A=R+Y+gamma*v; C=R-Z+nu*v; W=R*(Y+Z)+mu*v; N=V*(Y+Z)+ss*mu
    Dh=mu+R*(nu-gamma);nh=A*(R-Z)+C*(R-Y);B0=2+(1-beta)*v
    fraka=R*(1+q)+V*v; frakc=V+beta*R
    u0=r*A+C*(R-Y);u1=C*gamma;d1=1-V-beta*eps;ah=eps*(1+q)-(1-V)*v
    dS=V+beta*(eps-v);sh=p*q+1+v-fraka;Bs=B0+(1+beta)*ss;Ds=fraka+frakc*ss
    c0=N*A*A*B0-V*W*u0*fraka
    c1=N*A*A*(1+beta)-V*W*(u0*frakc+u1*fraka)
    c2=-V*W*u1*frakc
    vw_j=N*q-(V+T)*(ss*R-V*v); Pguard=V*W-vw_j-beta*ss*W
    gs=[beta-ss,T,nu,gamma,mu,ss-v,V-ss,B0-A,
        (ss-V*v)*mu-eps*V*(Y+Z),d1,(1-V)*(ss+v)-eps*(2+beta*(ss-v)),Dh,
        beta*ss-ss*ss-eps*beta,3-2*R-beta,(1+beta)*Y-V,1-p*Y+V,
        ss*Dh-beta*nh,sh*Dh-nh*dS,N*A*B0*Dh-V*W*(u0*Dh+u1*nh),
        N*A*B0*d1-V*W*(u0*d1+u1*ah),Pguard,vw_j,
        p*q*V*W-N*q*A+vw_j*(A-1-v),q*Y+V*(1+v)-V*A,
        N*A*A*Bs*Dh-V*W*Ds*(u0*Dh+u1*nh),A*Bs-(1+v)*Ds,
        c1*c1-4*c0*c2,9*V*W-4*N*A,(9*A-4*u0)*Dh-4*u1*nh,
        (1-T)*V*W-C*N,(3-r)*V-ss,17*q-16*R-16*V*v+16*v*(1+beta),
        B0*(R+V*v)-A*(1+v),(R+V*v-q)*B0+A*(p*q-1-v),gamma-nu]
    return gs,c0+c1*ss+c2*ss*ss,c1+2*c2*ss

def exact_rows(lo,hi,f):
    center=[(lo[i]+hi[i])/2 for i in range(NV)]; rad=[(hi[i]-lo[i])/2 for i in range(NV)]
    xb=[D.var(i,lo[i],hi[i]) for i in range(NV)]
    gb,g35b,g36b=guards_generic(xb,f)
    xc=[D.var(i,center[i],center[i]) for i in range(NV)]
    gc,g35c,g36c=guards_generic(xc,f)
    usable=list(range(35)); G=gb; C=gc
    if g36b.v.lo>=0:
        usable.append(35); G=gb+[g35b]; C=gc+[g35c]
    for j in usable:
        if G[j].v.hi<0:
            return {'kind':'interval','guard':j,'upper':G[j].v.hi},None
    rows=[]
    for j in usable:
        extra=Q(0); aa=[]
        for i in range(NV):
            di=G[j].d[i]; mid=(di.lo+di.hi)/2; err=(di.hi-di.lo)/2
            aa.append(rad[i]*mid); extra += rad[i]*err
        rows.append((C[j].v.lo+extra,aa,j))
    return None,rows

def combo_margin(weights,rows):
    mp={j:(bb,a) for bb,a,j in rows}
    B=Q(0); A=[Q(0) for _ in range(NV)]
    for j,w in weights:
        if j not in mp: raise ValueError(f'guard {j} not usable on this box')
        bb,a=mp[j]; B += Q(w)*bb
        for i in range(NV): A[i] += Q(w)*a[i]
    return B+sum(abs(x) for x in A)
