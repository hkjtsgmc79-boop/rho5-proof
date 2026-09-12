"""Independent exact matrix/canonical witness checks, no numerical tolerance."""
from fractions import Fraction as Q
import json,sys
from pathlib import Path
R=Path(__file__).resolve().parent
sys.path.insert(0,str(R/'support'))
import structural_rules as sr
from exact_interval import I,serial

def ensure(b,msg):
 if not b:raise ValueError(msg)

def reconstruct(z):
 p,e,be,k=z['p'],z['e'],z['beta'],z['k'];u=[z['u'+str(i)]for i in range(3)];x=[z['x'+str(i)]for i in range(3)];v=[z['v'+str(i)]for i in range(3)];q=[z['q'+str(i)]for i in range(3)]
 A,B,c,d,r,s,t=[z[n]for n in ('A','B','c','d','r','s','t')]
 D=[[k,A,B],[c*k,r+c*A,s+c*B],[d*k,t+d*A,-r+d*B]]
 S=[[D[i][j]+x[i]*q[j]for j in range(3)]for i in range(3)]
 M=[[Q(1),-e,*v],[be,p-e*be,*[q[j]+be*v[j]for j in range(3)]]]
 M += [[u[i],p*x[i]-e*u[i],*[S[i][j]+u[i]*v[j]for j in range(3)]]for i in range(3)]
 return M

def matmul(A,B):return [[sum(a*b for a,b in zip(row,col))for col in zip(*B)]for row in A]
def transp(A):return [list(z)for z in zip(*A)]
def eye(n):return [[Q(int(i==j))for j in range(n)]for i in range(n)]
def diag(v):return [[Q(v[i]if i==j else 0)for j in range(len(v))]for i in range(len(v))]
def direct_rep(M,tag):
 t=int(tag[1]);d=int(tag[3]);ss=[1 if x=='+'else-1 for x in tag[5:]]
 if t:
  J=diag([1,-1,1,1,1]);M=matmul(matmul(J,transp(M)),J)
 if d:
  J=eye(5);J[3][3]=J[4][4]=0;J[3][4]=-1;J[4][3]=1
  M=matmul(matmul(J,M),J)
 E=diag([1,ss[0],ss[1],ss[2],ss[2]])
 return matmul(matmul(E,M),E)

def check_cp(M):
 C=[row[:]for row in M];pivs=[]
 ensure(max(abs(v)for row in C for v in row)==1,'raw norm differs')
 for i in range(5):
  p=C[i][i];ensure(p!=0,'zero pivot');ensure(abs(p)==max(abs(C[a][b])for a in range(i,5)for b in range(i,5)),'not CP')
  pivs.append(p)
  for a in range(i+1,5):
   for b in range(i+1,5):C[a][b]-=C[a][i]*C[i][b]/p
 return pivs

def interval_intersect_1d(rows,lo,hi):
 # |a z+b|<=C, exact common intersection incl a=0
 for a,b,C in rows:
  if a==0:ensure(abs(b)<=C,'constant interval violated');continue
  x,y=(-C-b)/a,(C-b)/a;lo=max(lo,min(x,y));hi=min(hi,max(x,y))
 ensure(lo<=hi,'empty interval')
 return lo,hi

def canonical(z):
 # V37: beta endpoint; prefix 2D polygon vertices; maximum p then min e;
 # common tail maxima. Does not import previous witness implementation.
 zz=z.copy();u=[z['u'+str(i)]for i in range(3)];x=[z['x'+str(i)]for i in range(3)];v=[z['v'+str(i)]for i in range(3)];q=[z['q'+str(i)]for i in range(3)]
 be=interval_intersect_1d([(v[j],q[j],Q(1))for j in range(3)],Q(0),Q(1))[1];zz['beta']=be
 # all prefix inequalities a*p+b*e<=c, 0<=e<=1,0<=p<=2
 hs=[(Q(0),Q(1),Q(1)),(Q(0),Q(-1),Q(0)),(Q(-1),Q(0),Q(0)),(Q(1),Q(0),Q(2))]
 for a,b in [(Q(1),-be)]+[(x[i],-u[i])for i in range(3)]:hs +=[(a,b,Q(1)),(-a,-b,Q(1))]
 verts=[]
 for i,(a,b,c)in enumerate(hs):
  for d,f,g in hs[:i]:
   de=a*f-d*b
   if de==0:continue
   p=(c*f-g*b)/de;e=(a*g-d*c)/de
   if all(aa*p+bb*e<=cc for aa,bb,cc in hs):verts.append((p,e))
 ensure(verts,'empty prefix');p=max(a for a,b in verts);e=min(b for a,b in verts if a==p);zz['p']=p;zz['e']=e
 k,A,B,c,d=[z[n]for n in ('k','A','B','c','d')]
 lo=[[max(-k,-p-x[i]*q[j],-1-x[i]*q[j]-u[i]*v[j])for j in range(3)]for i in range(3)]
 hi=[[min(k,p-x[i]*q[j],1-x[i]*q[j]-u[i]*v[j])for j in range(3)]for i in range(3)]
 for i,j,t in [(0,0,k),(0,1,A),(0,2,B),(1,0,c*k),(2,0,d*k)]:ensure(lo[i][j]<=t<=hi[i][j],'fixed core not physical')
 r=min(hi[1][1]-c*A,d*B-lo[2][2]);rlo=max(Q(0),lo[1][1]-c*A,d*B-hi[2][2]);s=min(r,hi[1][2]-c*B);t=min(r,hi[2][1]-d*A)
 ensure(r>0 and r>=rlo and s>=max(Q(0),lo[1][2]-c*B)and t>=max(Q(0),lo[2][1]-d*A),'empty tail')
 zz.update(r=r,s=s,t=t,F=r+s*t/r)
 return zz

def read_control(c):
 z={n:Q(v)for n,v in zip(c['point_gap_order'],c['point_gap'])};z['s']=z['r']-z['sigma'];z['t']=z['r']-z['tau'];z['F']=z['r']+z['s']*z['t']/z['r'];return z

if __name__=='__main__':
 rec=json.loads((R/'SOURCE_REBUILD.json').read_text())['records'][0]
 control=json.loads((R/'HIGH_CONTROLS16.json').read_text())['cases'][6]
 z=read_control(control);M=reconstruct(z);ensure(M==[[Q(v)for v in row]for row in control['matrix']],'stored matrix mismatch')
 pivs=check_cp(M);zz=canonical(z)
 ensure(0<z['s']<z['r'] and 0<z['t']<z['r'],'not strict proper B')
 ensure(z['u0']*z['x1']-z['u1']*z['x0']!=0,'left receiver is not rank two')
 ensure(z['v0']*z['q1']-z['v1']*z['q0']!=0,'right receiver is not rank two')
 diffs={n:[str(z[n]),str(zz[n])]for n in sr.ORDER if z[n]!=zz[n]}
 print('canonical diffs',diffs)
 ensure(not diffs,'not V37 canonical')
 parent=json.loads((R/'data'/rec['parent_file']).read_text()); frame=control['frame_order']
 print('parent keys',parent.keys())
 ensure(all(Q(lo)<=z[n]<=Q(hi)for n,(lo,hi)in zip(frame,parent['box'])),'B17 parent mismatch')
 ensure(all(Q(lo)<=z[n]<=Q(hi)for n,(lo,hi)in zip(sr.ORDER,rec['aux_image'])),'B24 target mismatch')
 # center identity and old port in frozen source
 sys.path.insert(0,str(R/'data/deep'));import deep_math as dm;bp=dm.load_protocol(R/'data/deep')
 centers=[[Q(v)for v in row]for row in json.loads((R/'centers.json').read_text())]
 ensure(centers==bp.fs.CENTERS,'center mismatch')
 ensure(Q(4132517,1000000)<z['F']<bp.fs.ALPHA,'height not gamma-alpha')
 origport=bp.fs.safe_port(rec['aux_image']);print('old literal',origport)
 # 32 transformations exact matrices and CP
 for tag,zzI in sr.representations({n:I(z[n])for n in sr.ORDER}):
  zz={n:v.lo for n,v in zzI.items()};MR=direct_rep(M,tag)
  ensure(reconstruct(zz)==MR,'rep matrix mismatch '+tag);newp=check_cp(MR);ensure(abs(newp[-1])==z['F'],'rep height changed')
 # save witness exact complete scalar source (not merely box point)
 out={'status':'EXACT_COMPLETE_CANONICAL_GAMMA_WITNESS_IN_STARTER_0','origin':'PHYSICAL_HIGH_CONTROLS16 record_index=6; existing witness newly source-bound','source_ordinal':0,'parent_index':rec['index'],'path':rec['path'],'source_image_sha256':rec['image_sha256'],'projection_sha256':rec['projection_sha256'],'parent_raw_sha256':rec['parent_raw_sha256'],'B24':{n:str(z[n])for n in sr.ORDER},'matrix':serial(M),'pivots':serial(pivs),'canonical_recomputed':True,'original_B17_inclusion':True,'rebuilt_B24_inclusion':True,'F':str(z['F']),'all_32_exact_matrix_representations_checked':True,'old_literal_safe_port':origport,'left_receiver_minor':str(z['u0']*z['x1']-z['u1']*z['x0']),'right_receiver_minor':str(z['v0']*z['q1']-z['v1']*z['q0'])}
 (R/'WITNESS_MEMBERSHIP.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');print('WITNESS PROVED',float(z['F']))
