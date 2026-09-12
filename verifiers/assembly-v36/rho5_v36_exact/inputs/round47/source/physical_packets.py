"""Necessary bounded rank-one packets from ONE native X box.
All interval intersections preserve every actual source. Solving each packet is
not sufficient for simultaneous physical completion (p,D,S,O remain coupled).
"""
from fractions import Fraction as Q
from factor_feasibility import Interval,solve

def add(a,b):return(a[0]+b[0],a[1]+b[1])
def sub(a,b):return(a[0]-b[1],a[1]-b[0])
def mul(a,b):
 p=[x*y for x in a for y in b];return(min(p),max(p))
def meet(a,b):return(max(a[0],b[0]),min(a[1],b[1]))
def bad(a):return a[0]>a[1]

def build_packets(bounds,typ):
 b=[tuple(map(Q,z))for z in bounds]
 if len(b)!=23 or typ not in ('I','II'):raise ValueError('requires V34 23-coordinate dictionary')
 one=(Q(-1),Q(1));pb=(-b[7][1],b[7][1]);kb=(-b[0][1],b[0][1]);zero=(Q(0),Q(0))
 if b[0][0]<=0 or b[7][0]<=0:raise ValueError('positive p and k required')
 # Core factor packet (c,d) x (k,A,B).
 C=[[mul(b[5+i],b[j])for j in (0,3,4)]for i in range(2)]
 # Stage augmented packet (1,x0,x1,x2) x (p,q0,q1,q2).
 X=[[b[j]for j in (7,19,20,21)]]+[[mul(b[13+i],b[j])for j in (7,19,20,21)]for i in range(3)]
 # Original augmented packet (beta,u0,u1,u2) x (e,v0,v1,v2).
 Y=[[mul(b[i],b[j])for j in (8,16,17,18)]for i in (9,10,11,12)]
 Y[0][0]=meet(Y[0][0],sub(b[7],one))
 Y[0 if typ=='I' else 1][0]=meet(Y[0 if typ=='I' else 1][0],b[22])
 D=[[b[j]for j in (0,3,4)]]
 for i in range(2):D.append([C[i][0]]+[add(b[2 if (i==1 and j==1)else 1],C[i][j+1])for j in range(2)])
 S=[[pb for j in range(3)]for i in range(3)]
 O=[[one for j in range(3)]for i in range(3)]
 for _ in range(3):
  for i in range(3):
   Y[i+1][0]=meet(Y[i+1][0],sub(X[i+1][0],one))
   X[i+1][0]=meet(X[i+1][0],add(Y[i+1][0],one))
   Y[0][i+1]=meet(Y[0][i+1],sub(one,b[19+i]))
   for j in range(3):
    D[i][j]=meet(D[i][j],kb)
    S[i][j]=meet(S[i][j],meet(add(D[i][j],X[i+1][j+1]),pb))
    O[i][j]=meet(O[i][j],add(S[i][j],Y[i+1][j+1]))
    if any(bad(z)for z in (D[i][j],S[i][j],O[i][j],X[i+1][j+1],Y[i+1][j+1])):return None,'direct_DSO'
    Y[i+1][j+1]=meet(Y[i+1][j+1],sub(O[i][j],S[i][j]))
    S[i][j]=meet(S[i][j],sub(O[i][j],Y[i+1][j+1]))
    X[i+1][j+1]=meet(X[i+1][j+1],sub(S[i][j],D[i][j]))
    D[i][j]=meet(D[i][j],sub(S[i][j],X[i+1][j+1]))
    if i:
     H=zero if j==0 else b[2 if(i==2 and j==2)else 1]
     C[i-1][j]=meet(C[i-1][j],sub(D[i][j],H))
     D[i][j]=meet(D[i][j],add(C[i-1][j],H))
  if any(bad(z)for M in (C,X,Y,D,S,O)for row in M for z in row):return None,'direct_interval'
 packets=[{'name':'stage4','left':[(Q(1),Q(1))]+b[13:16],'right':[b[7]]+b[19:22],'cells':X},
          {'name':'original4','left':[b[9]]+b[10:13],'right':[b[8]]+b[16:19],'cells':Y},
          {'name':'core23','left':b[5:7],'right':[b[0],b[3],b[4]],'cells':C}]
 return packets,None

def solve_box(bounds,typ):
 packets,error=build_packets(bounds,typ)
 if error:return {'status':'EXCLUDED','layer':3,'reason':error}
 results=[]
 for n,p in enumerate(packets):
  L=[Interval(*x)for x in p['left']];R=[Interval(*x)for x in p['right']];C=[[Interval(*x)for x in row]for row in p['cells']]
  cert=solve(L,R,C)
  if cert['status']=='UNSAT':return {'status':'EXCLUDED','layer':n,'packet':p,'certificate':cert}
  results.append(cert)
 return {'status':'NOT_EXCLUDED','packet_witnesses':results}
