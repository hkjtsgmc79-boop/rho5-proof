"""24-variable actual CP model near X: s=r-sigma, t=r-tau.
No new source assumption is encoded by selected contact labels.
"""
from fractions import Fraction as Q
from support.x_local_model import add,scale,neg,mul,const,ev,diff
from support import x_local_model as X
NAMES=X.NAMES+('sigma','tau')
def var(n):return {(NAMES.index(n),):Q(1)}
def source():
 out=X.source()
 for block,cell,gap in [('D','12','sigma'),('S','12','sigma'),('O','12','sigma'),('D','21','tau'),('S','21','tau'),('O','21','tau')]:
  out[block+cell+'+']=add(out[block+cell+'+'],var(gap))
  out[block+cell+'-']=add(out[block+cell+'-'],neg(var(gap)))
 out['sigma']=var('sigma');out['tau']=var('tau')
 out['positive_s']=add(var('r'),neg(var('sigma')))
 out['positive_t']=add(var('r'),neg(var('tau')))
 return out

def physical_matrix(z):
 z=list(map(Q,z));d=dict(zip(NAMES,z))
 k,r,w,A,B,c,h,p,e,be=z[:10];u=z[10:13];x=z[13:16];v=z[16:19];q=z[19:22];sg,tg=z[22:24]
 D=[[k,A,B],[c*k,r+c*A,r-sg+c*B],[h*k,r-tg+h*A,w+h*B]]
 S=[[D[i][j]+x[i]*q[j] for j in range(3)] for i in range(3)]
 O=[[S[i][j]+u[i]*v[j] for j in range(3)] for i in range(3)]
 M=[[Q(1),-e]+v,[be,p-e*be]+[q[j]+be*v[j] for j in range(3)]]
 M += [[u[i],p*x[i]-e*u[i]]+O[i] for i in range(3)]
 return M,D,S,O

def height(z):
 z=list(map(Q,z));r,w=z[1:3];sg,tg=z[22:24]
 return (r-sg)*(r-tg)/r-w

def check_actual(z):
 z=list(map(Q,z));assert len(z)==24
 values={n:ev(g,z) for n,g in source().items()}
 for n,v in values.items(): assert v>=0,(n,str(v))
 assert min(z[0],z[1],z[7])>0
 M,D,S,O=physical_matrix(z);W=M;piv=[]
 for it in range(5):
  pv=W[0][0];assert pv!=0
  assert max(abs(x) for row in W for x in row)<=abs(pv),(it,pv)
  piv.append(pv);W=[[W[i][j]-W[i][0]*W[0][j]/pv for j in range(1,len(W))] for i in range(1,len(W))]
 assert piv[:4]==[Q(1),z[7],z[0],z[1]]
 assert abs(piv[4])==height(z)
 return {'pivots':list(map(str,piv)),'height':str(height(z)),'minimum_slack':str(min(values.values())),'matrix':[[str(v)for v in row]for row in M]}
