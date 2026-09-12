from pathlib import Path
import json,sys
from fractions import Fraction as Q
R=Path(__file__).resolve().parent
sys.path.insert(0,str(R/'support'));import structural_rules as sr
from exact_interval import I,serial
from matrix_audit import reconstruct,check_cp,ensure,matmul,eye,read_control
from transport_local import sorted_R,sorted_branches,XORDER

def reconstruct_X(z):
 p,e,be,k=z['p'],z['e'],z['beta'],z['k'];A,B,c,d,r,w=[z[n]for n in ('A','B','c','d','r','w')]
 u=[z['u'+str(i)]for i in range(3)];x=[z['x'+str(i)]for i in range(3)];v=[z['v'+str(i)]for i in range(3)];q=[z['q'+str(i)]for i in range(3)]
 D=[[k,A,B],[c*k,r+c*A,r+c*B],[d*k,r+d*A,w+d*B]]
 return [[Q(1),-e,*v],[be,p-e*be,*[q[j]+be*v[j]for j in range(3)]]]+[[u[i],p*x[i]-e*u[i],*[D[i][j]+x[i]*q[j]+u[i]*v[j]for j in range(3)]]for i in range(3)]

controls=[read_control(json.loads((R/'HIGH_CONTROLS16.json').read_text())['cases'][6])]
for s,t in [(Q(0),Q(0)),(Q(0),Q(1,2)),(Q(1,2),Q(0)),(Q(1,2),Q(1,2)),(Q(1,4),Q(1,4)),(Q(1,3),Q(1,4)),(Q(1,4),Q(1,3))]:
 z={n:Q(0)for n in sr.ORDER};z.update(p=Q(1),k=Q(1),r=Q(1,2),s=s,t=t,F=Q(1,2)+2*s*t);controls.append(z)
count=0;maxell=Q(0)
for i,z in enumerate(controls):
 check_cp(reconstruct(z))
 for tag,zz in sr.representations({n:I(z[n])for n in sr.ORDER}):
  for br,zs in sorted_branches(zz):
   target,ell,co=sorted_R(zs);y={n:v.lo for n,v in zip(XORDER,target)};sval={n:v.lo for n,v in zs.items()};M=reconstruct(sval)
   G=eye(5);G[3][3]=co['lambda'].lo;G[3][4]=-co['mu'].lo;G[4][3]=-co['nu'].lo;G[4][4]=-co['xi'].lo
   P=eye(5);P[3][3]=P[4][4]=0;P[3][4]=P[4][3]=1
   X=matmul(matmul(G,M),P)
   ensure(X==reconstruct_X(y),'direct R matrix mismatch')
   pp=check_cp(X);ensure(abs(pp[-1])==y['r']-y['w'],'target height mismatch')
   ensure(sval['F']-abs(pp[-1])==ell.lo==ell.hi,'loss identity mismatch')
   ensure(ell.lo>=0,'negative loss');count+=1;maxell=max(maxell,ell.lo)
result={'status':'EXACT_TRANSPORT_CONTROLS_PASSED','complete_B_controls':len(controls),'actual_representation_R_matrix_comparisons':count,'max_loss':str(maxell),'tail_zero_equality_both_orderings_included':True,'general_transport_theorem_not_claimed_proved_by_samples':True}
(R/'TRANSPORT_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
