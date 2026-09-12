"""Exact complete negative-D tail fibre for fixed shared head and core arms.
Domain: H=[[r,s],[t,-r]], 0<=s,t<=r. No flag/rank assumptions.
"""
from fractions import Fraction as Q
from gap_model import NAMES,physical_matrix,check_actual,height

def cell_intervals(z):
 z=list(map(Q,z));k,p=z[0],z[7];u=z[10:13];x=z[13:16];v=z[16:19];q=z[19:22]
 L=[];U=[];Ll=[];Ul=[]
 for i in range(3):
  ll=[];uu=[];lll=[];uul=[]
  for j in range(3):
   low={'D':-k,'S':-p-x[i]*q[j],'O':-1-x[i]*q[j]-u[i]*v[j]}
   high={'D':k,'S':p-x[i]*q[j],'O':1-x[i]*q[j]-u[i]*v[j]}
   a=max(low.values());b=min(high.values());ll.append(a);uu.append(b)
   lll.append([n for n,value in low.items()if value==a]);uul.append([n for n,value in high.items()if value==b])
  L.append(ll);U.append(uu);Ll.append(lll);Ul.append(uul)
 return L,U,Ll,Ul

def maximize_tail(z):
 z=list(map(Q,z));check_actual(z)
 assert z[2]==-z[1], 'negative D-chart required'
 k,r,w,A,B,c,d=z[:7];s=r-z[22];t=r-z[23]
 assert 0<=s<=r and 0<=t<=r
 L,U,Ll,Ul=cell_intervals(z)
 rl=max(Q(0),L[1][1]-c*A,d*B-U[2][2])
 rh=min(U[1][1]-c*A,d*B-L[2][2])
 sl=max(Q(0),L[1][2]-c*B);su=U[1][2]-c*B
 tl=max(Q(0),L[2][1]-d*A);tu=U[2][1]-d*A
 assert rl<=r<=rh and sl<=s<=su and tl<=t<=tu
 rr=rh;ss=min(rr,su);tt=min(rr,tu)
 assert rr>0 and ss>=sl and tt>=tl
 out=z[:];out[1]=rr;out[2]=-rr;out[22]=rr-ss;out[23]=rr-tt
 target=check_actual(out);assert height(out)>=height(z)
 # r-upper providers: D/S/O at (1,1) upper or (2,2) lower.
 providers=[]
 if rh==U[1][1]-c*A:providers += [x+'11+'for x in Ul[1][1]]
 if rh==d*B-L[2][2]:providers += [x+'22-'for x in Ll[2][2]]
 assert providers
 face=(ss==rr or tt==rr)
 return {'point':out,'r_bounds':(rl,rh),'s_bounds':(sl,su),'t_bounds':(tl,tu),
   'height':height(out),'source_height':height(z),'r_contacts':providers,
   's_contacts':(['s=r']if ss==rr else[x+'12+'for x in Ul[1][2]]),
   't_contacts':(['t=r']if tt==rr else[x+'21+'for x in Ul[2][1]]),
   'paid_face':face,'matrix':target['matrix']}

def interpolation(z,theta):
 theta=Q(theta);assert 0<=theta<=1
 z=list(map(Q,z));end=maximize_tail(z)['point']
 r0,s0,t0=z[1],z[1]-z[22],z[1]-z[23]
 r1,s1,t1=end[1],end[1]-end[22],end[1]-end[23]
 rr=r0+theta*(r1-r0);ss=s0+theta*(s1-s0);tt=t0+theta*(t1-t0)
 y=z[:];y[1]=rr;y[2]=-rr;y[22]=rr-ss;y[23]=rr-tt
 check_actual(y);assert height(y)>=height(z)
 return y
