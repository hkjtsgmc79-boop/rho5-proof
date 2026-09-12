#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as Q
from copy import deepcopy
import json
import sympy as S
from native_checker import native,build,blocks,residual,physical_slacks
from core_head_expansion import ceilings,reach,move,boundary_labels,validate
ROOT=Path(__file__).resolve().parent

def main():
    # Symbolic Schur and core-product invariance, with unscaled A,B.
    k,A,B,c,d,r,w,a,b=S.symbols('k A B c d r w a b',nonzero=True)
    D=S.Matrix([[k,A,B],[c*k,r+c*A,r+c*B],[d*k,r+d*A,w+d*B]])
    E=D.copy();E[0,0]=a*b*k
    for j in (1,2):E[0,j]*=a
    for i in (1,2):E[i,0]*=b
    n=0
    for i in (1,2):
        for j in (1,2):
            assert S.cancel(E[i,j]-E[i,0]*E[0,j]/E[0,0]-(D[i,j]-D[i,0]*D[0,j]/k))==0;n+=1
    for old,new in [(c*A,c/a*(a*A)),(c*B,c/a*(a*B)),(d*A,d/a*(a*A)),(d*B,d/a*(a*B))]:
        assert S.expand(old-new)==0;n+=1
    mats=json.loads((ROOT/'regression_matrices.json').read_text())
    W=json.loads((ROOT/'witness.json').read_text())['parameters']
    f=lambda key:Q(W[key]);u,x,v,q=[[Q(z) for z in W[key]] for key in ['u','x','vv','qq']]
    kk,AA,BB,cc,dd,rr,ww=[f(key) for key in ['k','A','B','c','d','r','w']]
    ss=dict(p=f('p'),e=f('e'),beta=f('beta'),u=u,x=x,v=v,q=q,k=kk,
            D=[[kk,AA,BB],[cc*kk,rr+cc*AA,rr+cc*BB],[dd*kk,rr+dd*AA,ww+dd*BB]])
    mats['handoff_new_nearpeak']=build(ss)
    # Independently valid low-height zero-arm controls; no use as high witnesses.
    for name,D0 in [('zero_arms',[[Q(1,2),0,0],[0,Q(1,4),Q(1,4)],[0,Q(1,4),-Q(1,4)]]),
                    ('one_zero_arm',[[Q(1,2),Q(1,8),0],[Q(1,8),Q(9,32),Q(1,4)],[0,Q(1,4),-Q(1,4)]])]:
        tmp=dict(p=Q(1),e=Q(0),beta=Q(0),u=[Q(0)]*3,x=[Q(0)]*3,v=[Q(0)]*3,q=[Q(0)]*3,D=D0,k=D0[0][0])
        mats[name]=build(tmp)
    records=[];count=0
    for name,M in mats.items():
        s=native(M);validate(s);caps=ceilings(s);F0=abs(blocks(build(s))[0][-1])
        for frac in [Q(0),Q(1,3),Q(1,2),Q(1)]:
            kap=s['k']+frac*(caps['kmax']-s['k']);z,par=reach(s,kap)
            assert all(val>=0 for _,val in physical_slacks(z))
            assert abs(blocks(build(z))[0][-1])==F0
            assert residual(s)==residual(z)
            count+=1
        end,par=reach(s,caps['kmax']);labels=boundary_labels(s,end)
        records.append({'name':name,'k':str(s['k']),'F':str(F0),'kmax':str(caps['kmax']),
            'kmax_display':float(caps['kmax']),'corner_cap':str(caps['corner_cap']),
            'arm_cap':None if caps['arm_cap'] is None else str(caps['arm_cap']),
            'scales':{key:str(val) for key,val in par.items()},'contacts':labels,
            'maximal_matrix':[[str(t) for t in row] for row in build(end)]})
        try:reach(s,caps['kmax']+Q(1,1000))
        except ValueError:pass
        else:raise AssertionError('over-cap target accepted')
    # A genuinely movable zero-arm source tests simultaneous-product construction.
    zero=next(x for x in records if x['name']=='zero_arms')
    assert Q(zero['kmax'])==1
    out={'status':'EXACT_CORE_HEAD_EXPANSION_COMPONENTS_PASS','symbolic_identities':n,'sources':len(mats),'full_path_matrices':count,'records':records}
    (ROOT/'logs/transport_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='records'}))
    for rec in records:print(rec['name'],'k=',float(Q(rec['k'])),'kmax=',rec['kmax_display'],'contacts=',rec['contacts'])
if __name__=='__main__':main()
