"""The full real X model. Polynomial source; no optimizer or high-r sign assumption."""
from fractions import Fraction as Q
NAMES=('k','r','w','A','B','c','d','p','e','beta', 'u0','u1','u2','x0','x1','x2','v0','v1','v2','q0','q1','q2')
# Each polynomial is a sparse dict from sorted variable-index tuples (degree <=2) to Fraction.
def add(*aa):
 z={}
 for a in aa:
  for m,c in a.items():z[m]=z.get(m,Q(0))+c
 return {m:c for m,c in z.items() if c}
def scale(a,q):return {m:c*Q(q) for m,c in a.items() if c*q}
def neg(a):return scale(a,-1)
def mul(a,b):
 z={}
 for m,c in a.items():
  for n,d in b.items():
   t=tuple(sorted(m+n));z[t]=z.get(t,Q(0))+c*d
 return {m:c for m,c in z.items() if c}
def const(q):return {():Q(q)} if q else {}
def var(n):return {(NAMES.index(n),):Q(1)}
def ev(a,z):
 out=Q(0)
 for mon,c in a.items():
  t=c
  for i in mon:t*=z[i]
  out+=t
 return out
def diff(a,i):
 z={}
 for m,c in a.items():
  count=m.count(i)
  if count:
   n=list(m);n.remove(i);n=tuple(n);z[n]=z.get(n,Q(0))+count*c
 return z
def source():
 Z={n:var(n) for n in NAMES};k,r,w,A,B,c,d,p,e,be=[Z[n] for n in NAMES[:10]]
 u,x,v,q=[[Z[t+str(i)] for i in range(3)] for t in ['u','x','v','q']]
 D=[[k,A,B],[mul(c,k),add(r,mul(c,A)),add(r,mul(c,B))],[mul(d,k),add(r,mul(d,A)),add(w,mul(d,B))]]
 S=[[add(D[i][j],mul(x[i],q[j])) for j in range(3)] for i in range(3)]
 O=[[add(S[i][j],mul(u[i],v[j])) for j in range(3)] for i in range(3)]
 rr={}
 def band(z,b,n):
  for sign,suf in [(-1,'+'),(1,'-')]:
   poly=add(b,scale(z,sign))
   if poly:rr[n+suf]=poly
 one=const(1)
 band(e,one,'e');band(be,one,'beta');band(add(p,neg(mul(e,be))),one,'head')
 for i in range(3):
  band(u[i],one,'u'+str(i));band(x[i],one,'x'+str(i));band(v[i],one,'v'+str(i));band(q[i],p,'q'+str(i))
  band(add(mul(p,x[i]),neg(mul(e,u[i]))),one,'L'+str(i));band(add(q[i],mul(be,v[i])),one,'P'+str(i))
  for j in range(3):
   band(D[i][j],k,f'D{i}{j}');band(S[i][j],p,f'S{i}{j}');band(O[i][j],one,f'O{i}{j}')
 rr['r+w']=add(r,w);rr['r-w']=add(r,neg(w))
 # positivity and domain, strict on the verified outer boxes
 for n in ('p','k','r'):rr['positive_'+n]=Z[n]
 return rr

def mv(M,v):return [sum((Q(M[i][j])*v[j] for j in range(len(v))),Q(0)) for i in range(len(M))]
def transpose(M):return list(map(list,zip(*M)))
# Maps from each raw local chart to the canonical R0 chart, valid as X maps on w=-r.
TAIL_MAPS=[([[1,0],[0,1]],[[1,0],[0,1]]),
 ([[1,0],[0,-1]],[[0,1],[1,0]]),
 ([[0,1],[1,0]],[[1,0],[0,-1]]),
 ([[0,1],[-1,0]],[[0,1],[-1,0]])]
def wall_transform(z,case,inverse=False):
 L,R=TAIL_MAPS[case]
 if inverse:L,R=transpose(L),transpose(R)
 out=list(z)
 for t in ('u','x'):
  ids=[NAMES.index(t+str(i)) for i in (1,2)];vals=mv(L,[z[i] for i in ids])
  for i,v in zip(ids,vals):out[i]=v
 for t in ('v','q'):
  ids=[NAMES.index(t+str(i)) for i in (1,2)];vals=mv(transpose(R),[z[i] for i in ids])
  for i,v in zip(ids,vals):out[i]=v
 for ns,T in [(('c','d'),L),(('A','B'),transpose(R))]:
  ids=[NAMES.index(n) for n in ns];vals=mv(T,[z[i] for i in ids])
  for i,v in zip(ids,vals):out[i]=v
 return out

def canonical_requirements():
 z={n:var(n) for n in NAMES};be=z['beta'];u=[z['u'+str(i)] for i in range(3)];x=[z['x'+str(i)] for i in range(3)]
 out={n:z[n] for n in ('beta','u0','u1','u2','x0','x1','x2')}
 out.update({n:neg(z[n]) for n in ('A','B','d')})
 out.update(delta=add(u[0],neg(mul(be,x[0]))),gamma=add(u[1],neg(mul(be,x[1]))),nu=add(mul(be,x[2]),neg(u[2])),tau=add(mul(u[0],x[1]),neg(mul(x[0],u[1]))),Delta=add(mul(u[0],x[2]),neg(mul(x[0],u[2]))),mu=add(mul(u[1],x[2]),neg(mul(x[1],u[2]))))
 return out
