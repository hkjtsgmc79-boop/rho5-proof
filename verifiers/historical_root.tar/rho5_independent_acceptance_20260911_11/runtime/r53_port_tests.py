from pathlib import Path
from fractions import Fraction as Q
from itertools import product
from collections import Counter
import json,os
import r53_port as p
b3,_,_=p.lg.source();b2=b3.b02;b1=b3.b01
ROOT=Path(__file__).resolve().parent

def point(z):return {n:p.I(v,v)for n,v in z.items()}
def exact(z,n):assert z[n].lo==z[n].hi;return z[n].lo

def main():
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 controls=json.loads((b3.DEP/'data/PHYSICAL_HIGH_CONTROLS16.json').read_text())['cases'];matrices=[[[Q(v)for v in row]for row in c['matrix']]for c in controls]
 rec=json.loads((ROOT/'v43/controls/proper_B_boundary.json').read_text());matrices.append([[Q(v)for v in row]for row in rec['matrix']])
 for name in ('OUTER_EXTENSION_CANONICAL','MIXED_STRICT_CANONICAL','HIGH_CANONICAL_CONTROL'):
  rec=json.loads((b3.ROOT/'data'/f'{name}.json').read_text());matrices.append([[Q(v)for v in row]for row in rec['matrix']])
 stats=Counter();J=b1.embed([[Q(0),Q(-1)],[Q(1),Q(0)]])
 for M in matrices:
  z=b2.native(M);z['F']=z['r']+z['s']*z['t']/z['r'];zi=point(z)
  for tr,sg in product((False,True),product((-1,1),repeat=3)):
   N=M
   if tr:
    N=b1.transpose(M);head=[1,-1,1,1,1];N=[[v*head[i]*head[j]for j,v in enumerate(row)]for i,row in enumerate(N)]
   N=b3.signed(N,sg);src=p.tb.diagonal(p.tb.transpose(zi)if tr else zi,sg)
   nn=b2.native(N)
   for n in p.tb.B_NAMES[:-1]:assert exact(src,n)==nn[n],('REP',n)
   for sw,ordered in p.tb.ordered_branches(src):
    O=b1.matmul(b1.matmul(J,N),J)if sw else N
    for route in ('R','D'):
     if route=='R':X,details=p.tb.target(ordered);ref=b1.contraction(O);loss=details['loss']
     else:
      X,details=p.bilateral(ordered);ref=b3.bilateral(O)
      assert (X is None)==(ref is None)
      if X is None:stats['D_unqualified']+=1;continue
      loss=p.I(*details['loss'])
     native=b2.native(ref['X_matrix'])
     for n in p.tb.X_NAMES:assert exact(X,n)==native[n],(route,n)
     assert loss.lo==loss.hi==ref['F']-ref['FX'];stats[route+'_exact_matrix_target_checks']+=1
 # Deterministic algebraic qualification edges; no claim these synthetic B24 boxes are physical.
 z=point(b2.native(matrices[-1]));z.update(r=p.I(1,1),s=p.I(1,1),t=p.I(1,1),F=p.I(2,2))
 out,meta=p.bilateral(z);assert out is not None and meta['Q']==['0','0']and meta['loss']==['0','0'];stats['D_closed_Q_equality']=1
 z['s']=p.I(0,0);z['t']=p.I(0,0);out,_=p.bilateral(z);assert out is None;stats['D_zero_s_rejected']=1
 z.update(s=p.I(Q(1,2),Q(1,2)),t=p.I(Q(1,2),Q(1,2)));out,meta=p.bilateral(z);assert out is None and meta['provably_Q_negative'];stats['D_negative_Q_rejected']=1
 z.update(r=p.I(1,1),s=p.I(Q(1,2),1),t=p.I(0,Q(1,2)));out,_=p.bilateral(z);assert out is None;stats['D_crossing_Q_not_assumed']=1
 # New proper-B P0 boundary source must be accepted by the combined, fully ordered interval diagnostic at singleton width.
 z=b2.native(matrices[16]);z['F']=z['r']+z['s']*z['t']/z['r'];got=p.check([[str(z[n]),str(z[n])]for n in p.tb.B_NAMES]);assert got['status']=='CANDIDATE_REQUIRES_ROOT_RULE';stats['V43_proper_B_point_port_positive']=1
 result={'status':'R53_INTERVAL_TRANSPORT_MATRIX_CONTROLS_PASS','full_physical_controls':len(matrices),'checks':dict(stats),'production_root_terminal_registered':False}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
