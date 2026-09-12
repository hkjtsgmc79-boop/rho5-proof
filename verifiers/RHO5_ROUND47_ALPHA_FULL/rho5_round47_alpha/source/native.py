"""Independent full-matrix rational checks and the declared 22-coordinate X dictionary."""
from fractions import Fraction as Q
from local_model import NAMES,source,ev

def rat(v):
 if isinstance(v,(float,bool)):raise TypeError('Exact integers or rational strings required')
 return Q(v)
def from_matrix(M):
 M=[[rat(x) for x in row] for row in M]
 assert len(M)==5 and all(len(row)==5 for row in M) and M[0][0]==1
 e=-M[0][1];be=M[1][0];p=M[1][1]+e*be;assert p>0
 u=[row[0] for row in M[2:]];v=M[0][2:];x=[(M[i+2][1]+e*u[i])/p for i in range(3)];q=[M[1][j+2]-be*v[j] for j in range(3)]
 D=[[M[i+2][j+2]-u[i]*v[j]-x[i]*q[j] for j in range(3)] for i in range(3)];k=D[0][0];assert k>0
 H=[[D[i][j]-D[i][0]*D[0][j]/k for j in (1,2)] for i in (1,2)]
 r=H[0][0];w=H[1][1];assert H[0][1]==H[1][0]==r and r>0 and abs(w)<=r
 vals=[k,r,w,D[0][1],D[0][2],D[1][0]/k,D[2][0]/k,p,e,be]+u+x+v+q
 assert len(vals)==22
 return vals

def to_matrix(z):
 z=list(map(rat,z));k,r,w,A,B,c,d,p,e,be=z[:10];u=z[10:13];x=z[13:16];v=z[16:19];q=z[19:22]
 D=[[k,A,B],[c*k,r+c*A,r+c*B],[d*k,r+d*A,w+d*B]]
 O=[[D[i][j]+x[i]*q[j]+u[i]*v[j] for j in range(3)] for i in range(3)]
 return [[Q(1),-e]+v,[be,p-e*be]+[q[j]+be*v[j] for j in range(3)]]+[[u[i],p*x[i]-e*u[i]]+O[i] for i in range(3)]

def verify_matrix(M):
 M=[[rat(x) for x in row] for row in M];z=from_matrix(M);assert to_matrix(z)==M
 B=M;piv=[];strict=[]
 for step in range(5):
  p=B[0][0];assert p!=0 and all(abs(x)<=abs(p) for row in B for x in row)
  strict.append(all(abs(B[i][j])<abs(p) for i in range(len(B)) for j in range(len(B)) if (i,j)!=(0,0)))
  piv.append(p)
  B=[[B[i][j]-B[i][0]*B[0][j]/p for j in range(1,len(B))] for i in range(1,len(B))]
 assert piv==[1,z[7],z[0],z[1],z[2]-z[1]]
 slacks={n:ev(g,z) for n,g in source().items()};assert all(x>=0 for x in slacks.values())
 for n in ('positive_p','positive_k','positive_r'):assert slacks[n]>0
 return {'point':z,'F':z[1]-z[2],'pivots':piv,'strict_first_three':all(strict[:3]),'slacks':slacks}

def gates(z):
 k,r,w,A,B,c,d,p,e,be=z[:10];U,V,T=z[10:13];X,Y,Z=z[13:16];v0,v1,v2=z[16:19];q0,q1,q2=z[19:22]
 L=[be*U*X,be*V*Y,be*T*Z,V*T,V*(V-be*Y),V*(be*Z-T),be*U*V*(U*Y-X*V),-U*V*A,-U*V*B,-U*V*d*k]
 R=[-e*v0*q0,-e*v1*q1,-e*v2*q2,v1*v2,v1*(p*v1+e*q1),v1*(-e*q2-p*v2),-e*v0*v1*(v0*q1-q0*v1),-v0*v1*c*k,-v0*v1*d*k,-v0*v1*B]
 return L,R
