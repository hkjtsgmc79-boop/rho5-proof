"""Small exact mathematical tests. The all-real statements are in THEOREMS.md."""
from fractions import Fraction as Q
from itertools import product
import random,json
import sympy as s
from source_access import fs,inherited
from dual_box import common_contract,rows_and_bounds,bound_value,dense_bound_value,apply_wave
from pivot_windows import WINDOW_ROWS,cycle_rows

def cp_pivots(matrix):
    a=[[Q(z)for z in row]for row in matrix];pivots=[]
    while a:
        m=len(a);i,j=max(((i,j)for i in range(m)for j in range(m)),key=lambda ij:abs(a[ij[0]][ij[1]]))
        if a[i][j]==0:break
        a[0],a[i]=a[i],a[0]
        for row in a:row[0],row[j]=row[j],row[0]
        q=a[0][0];assert all(abs(z)<=abs(q)for row in a for z in row)
        pivots.append(abs(q))
        a=[[a[i][j]-a[i][0]*a[0][j]/q for j in range(1,m)]for i in range(1,m)]
    return pivots

def run():
    assert inherited.FI == fs.NAMES.index('F') == 23
    assert len(fs.BASE_POLYS) == 106
    p,k,e,beta,u,v,x,h,z,G,lam,a,b,c=s.symbols('p k e beta u v x h z G lam a b c')
    S=k-x*h;O=S+u*v
    polynomials=[
      2-k+(beta-u)*v-((1-O)+(1-h+beta*v)+(1-x)*h),
      2-k+(e-v)*u-((1-O)+(1-p*x+e*u)+(1-h/p)*p*x),
      (u*(p+1-k)-beta*(p-1)-(u-beta)*(p-S)-beta*(1-(S-u*z))-u*(1-h-beta*z)-u*(1-x)*h),
      (1-(p-1)**2/G+p)-(p+1-(p-1)**2/G),
      a*((3-2*lam)*b+lam**2*a-c)-(3*a*b-b**2-a*c)-(b-lam*a)**2,
    ]
    for f in polynomials:assert s.cancel(f)==0
    # A sharp, fully CP 3x3 curve, for every rational point of this grid.
    sharp=0
    for i in range(65):
        q=Q(1)+Q(i,64)
        M=[[1,-1,q-1],[1,q-1,-1],[q-1,1,1]]
        A=[[Q(z)for z in row]for row in M];ps=[]
        while A:
            pivot=A[0][0];assert all(abs(z)<=abs(pivot)for row in A for z in row)
            ps.append(pivot)
            A=[[A[i][j]-A[i][0]*A[0][j]/pivot for j in range(1,len(A))]for i in range(1,len(A))]
        assert ps==[Q(1),q,q*(3-q)];sharp+=1
    rng=random.Random(410905);triples=0;matrices=0
    for n in(3,4,5):
      for _ in range(100):
        M=[[Q(rng.randrange(-5,6),5)for j in range(n)]for i in range(n)]
        pp=cp_pivots(M);matrices+=1
        for aa,bb,cc in zip(pp,pp[1:],pp[2:]):
            assert aa*cc<=bb*(3*aa-bb);triples+=1
    chsh=0
    for signs in product((-1,1),repeat=4):
      if s.prod(signs)!=-1:continue
      for vals in product((-1,1),repeat=4):
        f0,f1,g0,g1=vals
        assert signs[0]*f0*g0+signs[1]*f0*g1+signs[2]*f1*g0+signs[3]*f1*g1<=2;chsh+=1
    # Independently validate sparse vs dense residual bounds, all four signs/boundaries.
    rng=random.Random(4109);duals=0
    for _ in range(250):
      bs=[fs.I(Q(rng.randrange(-8,1),4),Q(rng.randrange(1,9),4))for i in range(24)]
      rows=[]
      for j in range(12):
        aa={i:Q(rng.randrange(-7,8),3)for i in range(24)}
        rows.append((aa,Q(rng.randrange(-9,10),3)))
      rec=dict(coordinate=rng.randrange(24),direction=rng.choice((-1,1)),objective_weight=rng.randrange(1,19),weights=[[j,rng.randrange(1,11)]for j in range(12)])
      value=bound_value(rows,bs,rec);assert value==dense_bound_value(rows,bs,rec);duals+=1
    # Preserve existing exact gamma-high complete B canonical states.
    import bootstrap
    from capacity import capacity,check_complete
    from interval_capacity import root_box
    source=json.loads((bootstrap.V39/'inputs/evidence/capacity_controls.json').read_text())
    controls=contain=physical_rows=0
    for item in source:
      f=[Q(z)for z in item['maximum']['frame']]
      if f[8]<0:f=f[:5]+[-z for z in f[5:]]
      out=capacity(f);assert out['status']=='COMPLETE_FIXED_FRAME_MAXIMUM'
      gap=[Q(z)for z in out['point_gap']];check_complete(gap)
      aux=[gap[0],gap[1],gap[1]-gap[22],gap[1]-gap[23],*gap[3:22],out['tail']['F']]
      assert out['tail']['F']>fs.GAMMA
      for _,pol in WINDOW_ROWS:assert fs.eval_point(pol,aux)>=0;physical_rows+=1
      for radius in (Q(0),Q(1,100000),Q(1,1000)):
        bx=[[str(max(rt.lo,z-radius)),str(min(rt.hi,z+radius))]for z,rt in zip(f,root_box())]
        parent=fs.parent_enclosure(bx)
        for profile in('BASE','PIVOT','CYCLE','PIVOT_CYCLE'):
          enclosed=common_contract(parent,profile=profile);assert enclosed['status']=='BOUNDED'
          assert all(Q(lo)<=v<=Q(hi)for v,(lo,hi)in zip(aux,enclosed['aux_image']));contain+=1
          # Test every lifted inequality on the same actual factors.
          rows,boxes=rows_and_bounds([[str(z),str(z)]for z in aux],profile=profile)
          assert all(z.lo==z.hi for z in boxes)
          point=[z.lo for z in boxes]
          assert all(sum(c*point[i]for i,c in a.items())<=b for a,b in rows)
          for _,pol in cycle_rows(enclosed['aux_image']):assert fs.eval_point(pol,aux)>=0;physical_rows+=1
      controls+=1
    return dict(symbolic_zero_identities=len(polynomials),sharp_three_pivot_curve_points=sharp,
      random_exact_CP_matrices=matrices,consecutive_window_checks=triples,
      CHSH_corner_checks=chsh,independent_dual_evaluation_controls=duals,
      inherited_complete_gamma_high_controls=controls,enclosure_checks=contain,
      exact_control_inequalities=physical_rows,not_a_global_height_proof=True)
if __name__=='__main__':print(json.dumps(run(),indent=2))
