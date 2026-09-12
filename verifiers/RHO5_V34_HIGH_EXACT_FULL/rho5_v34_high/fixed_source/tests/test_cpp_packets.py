from pathlib import Path
from fractions import Fraction as Q
import random,json,sys,subprocess,shutil,time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from factor_feasibility import Interval as I,solve,verify
ROOT=Path(__file__).resolve().parents[1];unit=(10**9)<<128;scale=unit*unit
exe=ROOT/'build_test/factor_probe'
rng=random.Random(340460);instances=[];known=[]
grid=[Q(i,4)for i in range(-4,5)]
for t in range(100):
 m=2+t%3;n=2+(t//3)%3
 L=[I(*sorted(rng.sample(grid,2)))for i in range(m)];R=[I(*sorted(rng.sample(grid,2)))for j in range(n)]
 C=[[I(*sorted(rng.sample(grid,2)))for j in range(n)]for i in range(m)]
 if t%5==0:
  a=[rng.choice([v for v in grid if L[i].contains(v)])for i in range(m)]
  b=[rng.choice([v for v in grid if R[j].contains(v)])for j in range(n)]
  C=[[I(min(z.lo,a[i]*b[j]),max(z.hi,a[i]*b[j]))for j,z in enumerate(row)]for i,row in enumerate(C)]
 ans=solve(L,R,C);verify(L,R,C,ans);known.append(ans['status']=='SAT');instances.append((L,R,C))
ob=json.loads((ROOT/'evidence/six_cycle_obstruction.json').read_text())
instances.append(([I(*a)for a in ob['left']],[I(*a)for a in ob['right']],[[I(*a)for a in r]for r in ob['cells']]));known.append(False)
def text(case):
 L,R,C=case
 def stri(z):
  lo=z.lo*scale;hi=z.hi*scale;assert lo.denominator==hi.denominator==1
  return f'{int(lo)} {int(hi)}'
 return f'{len(L)} {len(R)}\n'+'\n'.join(stri(z)for z in L+R+[z for row in C for z in row])+'\n'
t=time.time();p=subprocess.run([str(exe),'packet'],input=''.join(map(text,instances)),capture_output=True,text=True,check=True)
actual=[a=='1'for a in p.stdout.splitlines()];assert actual==known
print(json.dumps({'status':'CPP_FRACTION_PACKET_DIFFERENTIAL_PASS','cases':len(known),'sat':sum(known),'unsat':len(known)-sum(known),'seconds':time.time()-t}))
