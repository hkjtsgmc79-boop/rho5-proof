"""Exact algebra checks for the necessity map and V24 canonical reductions.
These identities do not on their own prove the six systems empty; the fixed
integer/linear-combination certificates are separately accepted.
"""
import sympy as s
from fractions import Fraction as F

def run():
 t,E,B,V,T,X,Y,Z,k,a,b,r,p,g,j,h,v,q=s.symbols('t E beta V T X Y Z k a b r p g j h v q')
 de=1-B*X;ga=V-B*Y;nu=B*Z-T;ta=Y-X*V;De=Z-T*X;mu=V*Z-T*Y
 d=t*X-Y;Q=t*de-ga;Om=t*De+E*ta-mu;ss=p-1;eps=r-2
 O00=k-X*j-g;O10=t*k-Y*j-V*g;O20=-E*k-Z*j-T*g
 O01=-a-X+de*h;O11=r-t*a-Y+ga*h;O21=r+E*a-Z-nu*h
 O02=-b+X*q+v;O12=r-t*b+Y*q+V*v;O22=-r+E*b+Z*q+T*v
 P0=-j-B*g;P2=q+B*v;S00=k-X*j;S10=t*k-Y*j
 e10=O10-1;e20=1+O20;e02=1+O02;e12=O12-1;e22=1+O22;eP=j+B*g-1
 z=1-P2;G=g-v
 checks=[]
 def ck(name,lhs,rhs=0):
  assert s.cancel(lhs-rhs)==0,name
  checks.append(name)
 ck('head_middle',T*(1-h)-eps-E*a-(1-O21)-Z*(p-1-B*h),1+T-p*Z)
 ck('tail_moment',(t-V)*v+d*q-(r-1-t),-e12+t*e02)
 ck('cofactor_moment',mu*G-(Y+Z)*eps-(t*Z+Y*E)*(k-b)-Y*e20,-Z*(e10+e12)+Y*e22)
 ck('tail_beta',E*b-eps-(1-Z)-Z*z-nu*v,e22)
 ck('first_o00_moment',mu*(1-O00)-(De+ta)*eps-Om*(k-b)-ta*e20,-De*e10+mu*e02-De*e12+ta*e22)
 ck('Pfirst',t*k-1-Y-ga*g,e10+Y*eP)
 ck('Ptail_gamma',ga*G-eps-t*(k-b)+Y*z,-e10-e12-Y*eP)
 ck('Ptail_nu',nu*G-eps-E*(k-b)-e20-Z*z,e22+Z*eP)
 ck('stage_Y',V*g-p+1,S10-p-e10)
 ck('stage_X',t*p-1-V*g+d*j,e10-t*(S00-p))
 ck('tail_cofactor_exact',mu+De+ta+Om*b-(De+ta)*r,mu*e02-De*e12+ta*e22)
 for lab,st,W,NC,DC in [('13',S00,X,p*ga+X*(V+B),ga+B*t*X),('23',S10,Y,p*ga+Y*(V+B),t*V)]:
  ck('K'+lab+' residual',DC*k-NC,ga*(st-p)+V*W*eP+B*W*e10)
 for lab,st,W,NC,DC in [('14',S00,X,p*mu+X*(V+T),mu+X*(V*E+T*t)),('24',S10,Y,p*mu+Y*(V+T),V*(t*Z+E*Y))]:
  ck('K'+lab+' residual',DC*k-NC,mu*(st-p)-V*W*e20+T*W*e10)
 ck('middle_spread',r-1-Y-t*(1-X)-Q*h+t*(1+O01),O11-1)
 ck('stage_order',X*Y*((k-p)/X-(t*k-p)/Y),p*(X-Y)-d*k)
 Br=eps+E*a
 ck('h_budget',Z*(h*(B-ss)-Br),1-O21+(1-Z)*(1-h+Br)+h*(1+T-p*Z))
 ck('k_9_4',s.Rational(9,4)-k,(1+ss+X*(1-B*ss)-k)+(B-s.Rational(1,2))**2+(B-ss)*(1-B)+(1-X)*(1-B*ss))
 KG=1+B+X*(1-B*B)-k
 ck('x_square',X*(1+X-k)+s.Rational(1,4),X*KG+(X*B-s.Rational(1,2))**2)
 # General slack-square payments; B0 and u0 are independent helper symbols.
 B0,u0=s.symbols('B0 u0');A=de*h;L=1+B0-X
 F1=(1+X*u0)**2-4*X*A-4*X**2*B0
 F2=A-4*X*A*L-4*X**2*B0*L
 F3=(1+X*u0)**2*(1-4*X*L)-4*X**2*B0
 ck('Ah first payment',F1,(2*X*h-1-X*u0)**2+4*X**2*(h*(B-ss)-B0)+4*X**2*h*(ss+u0-h))
 ck('Ah second payment',A*F2,(2*de*(A+X*B0)-A)**2+4*X*A*(A+X*B0)*(de*ss-L)+4*X*de**2*(A+X*B0)*(h*(B-ss)-B0))
 ck('Ah combined payment',F3,4*X*F2+(1-4*X*L)*F1)
 expr=4*X*(1+B0-X)+4*X**2*B0-1
 ck('X_four_fifths',expr.subs(B0,s.Rational(1,16)),-(3*X-1)*(5*X-4)/4)
 # Tail E direction with first-column contact denominators.
 NK14=p*mu+X*(V+T);DK14=mu+X*(V*E+T*t)
 NK24=p*mu+Y*(V+T);DK24=V*(t*Z+E*Y)
 ck('Omega K14 derivative',s.diff(Om*NK14/DK14,E),-NK14*mu*d/DK14**2)
 ck('Omega K24 derivative',s.diff(Om*NK24/DK24,E),-NK24*V*mu*d/DK24**2)
 at=1-Y+ga*(1+X)/de;ct=1+Z+nu*(1+X)/de;ell=nu-E*de
 LD=(nu*(r-at)+Q*(r-ct))/(de*(r-at))
 ck('least oblique endpoint',de*(r-at)*(E-LD),ell*at+Q*ct-(ell+Q)*r)
 ck('C0 positive payment',1+Z+E*(1+X)-r,(1+O22)+E*(1+O02)+(E*X+Z)*(1-P2)+ell*v)
 # Eleven-to-five middle specialization retains all discarded positive gaps.
 A1=1+Y+t*(1-X);C1=1+Y+t*(p-X);D1=ga+t*B*X
 A2=(t*(1+Z)+E*(1+Y))/(t+E);B2=(t*nu-E*ga)/(t+E)
 C2=(t*k+E*(1+Y))/(t+E);D2=E*ga/(t+E)
 R11=A1+Q*ss;R22=(B2*C2+D2*A2)/(B2+D2)
 ck('C1 redundant',C1-R11,(t-Q)*ss)
 ck('I1H redundant',A1+Q*ss/B-R11,Q*ss*(1-B)/B)
 ck('C2 redundant',B2*(C2-R22),D2*(R22-A2))
 # Positive-dependence coefficients of the two retained core capacities.
 R12=(Q*k+E*(de*(1+Y)+ga*(1-X)))/(Q+de*E)
 ck('core12 monotone K',s.diff(R12,k),Q/(Q+de*E))
 ck('core22 monotone K',s.diff(R22,k),(t*nu-E*ga)/(nu*(t+E)))
 # Rational root-box consequences independent of sampling.
 assert F(17,36)>F(15,32) and F(1,36)>F(1,64)
 assert F(1653,400)<F(4132517,1000000)
 assert F(16)*(F(1,2)**2)-F(17)*F(1,2)+4<0
 assert F(16)*(F(45,64)**2)-F(17)*F(45,64)+4<0
 return checks

if __name__=='__main__':
 a=run();print('Exact algebra checks:',len(a),'PASS')
 for n in a:print('PASS',n)
