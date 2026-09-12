from fractions import Fraction as Q
from pathlib import Path
import sys,json,random,copy
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from factor_feasibility import Interval as I,solve,verify
from itertools import combinations,product
ROOT=Path(__file__).resolve().parents[1]
left=[I(Q(1,4),Q(3,4))]*3;right=left[:]
cells=[[I(Q(1,16),Q(9,16)) for j in range(3)]for i in range(3)]
for i,j in [(0,0),(0,1),(1,1),(1,2),(2,2)]:cells[i][j]=I(Q(1,4),Q(1,4))
cells[2][0]=I(Q(5,16),Q(5,16))
rect=[]
for ii in combinations(range(3),2):
 for jj in combinations(range(3),2):
  a=cells[ii[0]][jj[0]].times(cells[ii[1]][jj[1]])
  b=cells[ii[0]][jj[1]].times(cells[ii[1]][jj[0]])
  assert max(a.lo,b.lo)<=min(a.hi,b.hi)
  rect.append([list(ii),list(jj),a.json(),b.json()])
for ii in combinations(range(3),2):
 for jj in combinations(range(3),2):
  ll=[left[i]for i in ii];rr=[right[j]for j in jj];cc=[[cells[i][j]for j in jj]for i in ii]
  local=solve(ll,rr,cc);assert local['status']=='SAT';verify(ll,rr,cc,local)
cert=solve(left,right,cells);assert cert['status']=='UNSAT';verify(left,right,cells,cert)
# Exact convex mixture of two legal factor configurations, before product-interval constraints.
am=[Q(1,2),Q(1,2),Q(1,4)];ap=[Q(1,2),Q(1,2),Q(3,4)]
bm=[Q(1,4),Q(1,2),Q(1,2)];bp=[Q(3,4),Q(1,2),Q(1,2)]
avg=[[(am[i]*bm[j]+ap[i]*bp[j])/2 for j in range(3)]for i in range(3)]
assert all(cells[i][j].contains(avg[i][j]) for i in range(3) for j in range(3))
for ii in combinations(range(3),2):
 for jj in combinations(range(3),2):
  for eps in product((-1,1),repeat=4):
   if eps[0]*eps[1]*eps[2]*eps[3]!=-1:continue
   assert sum(eps[2*a+b]*avg[ii[a]][jj[b]]for a in range(2)for b in range(2))<=2
(ROOT/'evidence/six_cycle_obstruction.json').write_text(json.dumps({'left':[a.json()for a in left],'right':[a.json()for a in right],'cells':[[a.json()for a in row]for row in cells], 'rectangle_tests':rect, 'convex_mixture':[[str(a)for a in row]for row in avg], 'certificate':cert},indent=2)+'\n')
# Deterministic exact generated instances; UNSAT is certified, SAT factors are explicitly checked.
rng=random.Random(34045);counts={'SAT':0,'UNSAT':0}
grid=[Q(i,4)for i in range(-4,5)]
for n in range(120):
 m=2+n%2;t=2+(n//2)%2
 L=[I(*sorted(rng.sample(grid,2)))for _ in range(m)]
 R=[I(*sorted(rng.sample(grid,2)))for _ in range(t)]
 C=[[I(*sorted(rng.sample(grid,2)))for _ in range(t)]for _ in range(m)]
 z=solve(L,R,C);verify(L,R,C,z);counts[z['status']]+=1
 # No grid witness may be missed by UNSAT. Exhaustive only for 2x2 cases.
 if m==2 and t==2:
  candidates=[[a for a in grid if I0.contains(a)]for I0 in L+R]
  for vals in product(*candidates):
   if all(C[i][j].contains(vals[i]*vals[m+j])for i in range(m)for j in range(t)):
    assert z['status']=='SAT';break
# Zero and single-point cases.
for L,R,C,status in [([I(0,0)],[I(-1,1)],[[I(0,0)]],'SAT'),
([I(0,0)],[I(-1,1)],[[I(1,1)]],'UNSAT'),
([I(-1,1),I(1,1)],[I(1,1)],[[I(0,0)],[I(1,1)]],'SAT'),
([I(1,1),I(1,1)],[I(1,1),I(1,1)],[[I(1,1),I(1,1)],[I(1,1),I(0,0)]],'UNSAT')]:
 z=solve(L,R,C);assert z['status']==status;verify(L,R,C,z)
# Rejection controls: no omissions, wrong product, nonclosed cycle, invalid SAT witness.
bad=copy.deepcopy(cert);bad['branches'].pop()
try:verify(left,right,cells,bad);raise AssertionError('accepted omitted branch')
except ValueError:pass
bad=copy.deepcopy(cert);r=next(a for a in bad['branches']if a['kind']=='negative_cycle');r['product']='1'
try:verify(left,right,cells,bad);raise AssertionError('accepted zero-margin cycle')
except ValueError:pass
bad=copy.deepcopy(cert);r=next(a for a in bad['branches']if a['kind']=='negative_cycle');r['cycle']=r['cycle'][:-1]
try:verify(left,right,cells,bad);raise AssertionError('accepted non-cycle')
except ValueError:pass
try:verify(left,right,cells,{'status':'SAT','left':['1/2']*3,'right':['1/2']*3});raise AssertionError('accepted inconsistent products')
except ValueError:pass
print(json.dumps({'status':'EXACT_FACTOR_FEASIBILITY_PASS','random_instances':counts,'six_cycle_rectangle_tests':len(rect),'zero_boundary_cases':4,'negative_controls':4}))
