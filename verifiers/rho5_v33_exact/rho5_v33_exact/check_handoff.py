import json, re, sys
from pathlib import Path
from fractions import Fraction as Q

text = Path(sys.argv[1]).read_text(encoding="utf-8")
def block(name):
    pat = r"<!-- BEGIN_"+name+r"_JSON -->\s*```json\s*(.*?)\s*```"
    return json.loads(re.search(pat, text, re.S).group(1))
alpha, witness = block("ALPHA"), block("WITNESS")
theta = witness["parameters"]
p,k,r,w,e,beta,A,B,c,d = [Q(theta[z]) for z in
    ("p","k","r","w","e","beta","A","B","c","d")]
u,x,v,q = [[Q(z) for z in theta[name]] for name in ("u","x","vv","qq")]
D = [[k,A,B],[c*k,r+c*A,r+c*B],[d*k,r+d*A,w+d*B]]
S = [[D[i][j]+x[i]*q[j] for j in range(3)] for i in range(3)]
O = [[S[i][j]+u[i]*v[j] for j in range(3)] for i in range(3)]
assert p>0 and k>0 and r>0 and abs(w)<=r
assert all(abs(z)<=1 for z in [e,beta,p-e*beta]+u+v+x)
assert all(abs(z)<=p for z in q)
assert all(abs(p*x[i]-e*u[i])<=1 for i in range(3))
assert all(abs(q[j]+beta*v[j])<=1 for j in range(3))
for T,h in [(D,k),(S,p),(O,Q(1))]:
    assert all(abs(z)<=h for row in T for z in row)
M = [[Q(1),-e]+v, [beta,p-e*beta]+[q[j]+beta*v[j] for j in range(3)]]
M += [[u[i],p*x[i]-e*u[i]]+O[i] for i in range(3)]
T = M
expected = [Q(1),p,k,r,w-r]
for step in range(5):
    pivot = T[0][0]
    assert pivot == expected[step]
    assert all(abs(z)<=abs(pivot) for row in T for z in row)
    if step<3:
        assert all(abs(T[i][j])<abs(pivot) for i in range(len(T))
                   for j in range(len(T)) if (i,j)!=(0,0))
    T = [[T[i][j]-T[i][0]*T[0][j]/pivot for j in range(1,len(T))]
         for i in range(1,len(T))]
F = r-w
assert F == Q(witness["F"])
assert Q(1653,400)<F<Q(4132517,1000000)<Q(alpha["isolating_interval"]["lower"])
assert Q(2)<k<Q(21,10) and r<k
assert len(alpha["minimal_polynomial"]["coefficients_ascending"])==62
# Exact closed-interval capacities from Appendix B; None denotes +infinity.
lo = [[max(-k,-p-x[i]*q[j],-1-x[i]*q[j]-u[i]*v[j])
       for j in range(3)] for i in range(3)]
hi = [[min(k,p-x[i]*q[j],1-x[i]*q[j]-u[i]*v[j])
       for j in range(3)] for i in range(3)]
aa = [[D[i][j]-lo[i][j] for j in range(3)] for i in range(3)]
bb = [[hi[i][j]-D[i][j] for j in range(3)] for i in range(3)]
def capacity(s,t,a,b):
    vals=[a[1]+max(s,0)*b[0]+max(-s,0)*a[0],
          a[2]+max(t,0)*b[0]+max(-t,0)*a[0]]
    if s*t<0:
        vals.append((abs(t)*a[1]+abs(s)*a[2])/(abs(s)+abs(t)))
    elif s*t>0 and abs(s)>abs(t):
        vals.append((abs(s)*a[2]+abs(t)*b[1])/(abs(s)-abs(t)))
    elif s*t>0 and abs(t)>abs(s):
        vals.append((abs(t)*a[1]+abs(s)*b[2])/(abs(t)-abs(s)))
    return min(vals)
CAB=min(capacity(c,d,[aa[i][j] for i in range(3)],
                    [bb[i][j] for i in range(3)]) for j in (1,2))
Ccd=min(capacity(A/k,B/k,aa[i],bb[i]) for i in (1,2))
assert r-F/2>max(CAB,Ccd)
print("PASS: exact full X, five CP pivots, strict first three,")
print("q_star < F < gamma < alpha_lower, and both fixed-block walls absent.")
print("No macro-class audit or whole-domain theorem is claimed by this check.")
