from fractions import Fraction as F
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
cert=json.load(open(HERE/'jacobian_recovered_certificate.json'))
names=['beta','V','s','Y','Z','v','h','b','R']; n=len(names); idx={k:i for i,k in enumerate(names)}
class I:
 __slots__=('lo','hi')
 def __init__(self,a,b=None):self.lo=F(a);self.hi=F(a if b is None else b);assert self.lo<=self.hi
 def __add__(self,o):o=ii(o);return I(self.lo+o.lo,self.hi+o.hi)
 __radd__=__add__
 def __neg__(self):return I(-self.hi,-self.lo)
 def __sub__(self,o):return self+(-ii(o))
 def __rsub__(self,o):return ii(o)-self
 def __mul__(self,o):o=ii(o);z=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi];return I(min(z),max(z))
 __rmul__=__mul__
 def inv(self):assert not self.lo<=0<=self.hi,(self.lo,self.hi);z=[1/self.lo,1/self.hi];return I(min(z),max(z))
 def __truediv__(self,o):return self*ii(o).inv()
 def __rtruediv__(self,o):return ii(o)/self
 def absmax(self):return max(abs(self.lo),abs(self.hi))
def ii(x):return x if isinstance(x,I) else I(x)
class J2:
 __slots__=('v','d','H')
 def __init__(self,v,d=None,H=None):
  self.v=ii(v); self.d=[I(0) for _ in range(n)] if d is None else d;self.H=[[I(0) for _ in range(n)] for __ in range(n)] if H is None else H
 @classmethod
 def var(cls,name,a,b):
  d=[I(0) for _ in range(n)];d[idx[name]]=I(1);return cls(I(a,b),d)
 def __add__(self,o):
  o=j2(o);return J2(self.v+o.v,[self.d[i]+o.d[i] for i in range(n)],[[self.H[i][j]+o.H[i][j] for j in range(n)] for i in range(n)])
 __radd__=__add__
 def __neg__(self):return J2(-self.v,[-x for x in self.d],[[-x for x in row] for row in self.H])
 def __sub__(self,o):return self+(-j2(o))
 def __rsub__(self,o):return j2(o)-self
 def __mul__(self,o):
  o=j2(o);d=[self.d[i]*o.v+self.v*o.d[i] for i in range(n)]
  H=[[self.H[i][j]*o.v+self.d[i]*o.d[j]+self.d[j]*o.d[i]+self.v*o.H[i][j] for j in range(n)] for i in range(n)]
  return J2(self.v*o.v,d,H)
 __rmul__=__mul__
 def inv(self):
  iv=self.v.inv();iv2=iv*iv;iv3=iv2*iv
  d=[-self.d[i]*iv2 for i in range(n)]
  H=[[2*self.d[i]*self.d[j]*iv3-self.H[i][j]*iv2 for j in range(n)] for i in range(n)]
  return J2(iv,d,H)
 def __truediv__(self,o):return self*j2(o).inv()
 def __rtruediv__(self,o):return j2(o)/self
def j2(x):return x if isinstance(x,J2) else J2(x)
def model(x):
 be=x['beta'];V=x['V'];s=x['s'];Y=x['Y'];Z=x['Z'];v=x['v'];h=x['h'];b=x['b'];R=x['R']
 r=R+1;p=1+s;T=p*Z-1;q=1-be*v;ga=V-be*Y;nu=be*Z-T;mu=V*Z-T*Y
 A=R+Y+ga*v;C=R-Z+nu*v;W=R*(Y+Z)+mu*v;N=V*(Y+Z)+s*mu
 lam=N/(V*W);B0=2+(1-be)*v;aa=R*(1+q)+V*v;cc=V+be*R;Dh=mu+R*(nu-ga);nh=A*(R-Z)+C*(R-Y)
 return [b-A,B0-b,lam-1,lam*b-r-C*(R-Y+ga*h)/A,A*(B0+(1+be)*h)-b*(aa+cc*h),A*(p*q+(1+v)*(1+be*h))-b*(aa+cc*h),Dh*h-nh,1-Z]
box={}
for k,(a,b) in cert['box'].items():box[{'be':'beta','ss':'s'}.get(k,k)]=(F(a),F(b))
cent={}
for k,val in cert['center'].items():cent[{'be':'beta','ss':'s'}.get(k,k)]=F(val)
XB={nm:J2.var(nm,*box[nm]) for nm in names}; GB=model(XB)
XC={nm:J2.var(nm,cent[nm],cent[nm]) for nm in names}; GC=model(XC)
jname=['beta','V','Y','Z','v','h','b','R']; ji=[idx[nm] for nm in jname]
# centered J intervals from center grad + hessian interval*radius all 9 vars
Jint=[[None]*8 for _ in range(8)]
for a in range(8):
 for j,jj in enumerate(ji):
  z=GC[a].d[jj]
  for k,nm in enumerate(names):
   rad=(box[nm][1]-box[nm][0])/2;z=z+GB[a].H[jj][k]*I(-rad,rad)
  Jint[a][j]=z
C0=[[F(z) for z in row] for row in cert['C0']];y0=[F(z) for z in cert['y0']];rho=[F(z) for z in cert['rho']]
E=[];rn=[]
for a in range(8):
 row=[]
 for bb in range(8):
  z=I(1 if a==bb else 0)
  for k in range(8):z=z-C0[k][a]*Jint[bb][k]
  row.append(z)
 E.append(row);rn.append(sum(z.absmax() for z in row))
assert max(rn) < F(7,50), max(rn)
# exact centered residual, center J is point intervals
res=[]
for a in range(8):
 zc=F(0)
 for k in range(8):
  rhs=F(1 if k==7 else 0)-sum(GC[m].d[ji[k]].lo*y0[m] for m in range(8))
  zc += C0[k][a]*rhs
 rad=abs(zc)
 # derivative wrt full 9 params from Hessian intervals
 for kk,nm in enumerate(names):
  di=I(0)
  for k in range(8):
   for m in range(8):di=di-C0[k][a]*y0[m]*GB[m].H[ji[k]][kk]
  xr=(box[nm][1]-box[nm][0])/2;rad+=di.absmax()*xr
 res.append(rad)
rat=[];ok=True
for i in range(8):
 im=res[i]+sum(E[i][j].absmax()*rho[j] for j in range(8));rat.append(float(im/rho[i]));ok &= im<rho[i] and y0[i]+rho[i]<F(-1,250)
assert ok and max(rat) < 1
out={
 'status':'PASS',
 'certificate':'reconstructed equivalent V26 global 9-parameter Jacobian interval certificate',
 'max_contraction_inf_row_norm':str(max(rn)),
 'max_contraction_inf_row_norm_decimal':float(max(rn)),
 'max_self_map_ratio_decimal':max(rat),
 'height_response_upper_bounds':[str(y0[i]+rho[i]) for i in range(8)],
 'claimed_response_bound':'all < -1/250',
 'box':cert['box']
}
(HERE/'jacobian_recovered_verification.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps(out,indent=2))
print('V26_RECONSTRUCTED_GLOBAL_JACOBIAN_CERTIFICATE_PASSED')
