"""Exact finite implementation checks, not a global height certificate."""
import json
from pathlib import Path
from fractions import Fraction as Q
from v27_exact import *

counts=dict(high_seed_states=0,orbit_states=0,strict_contractions=0,
            explicit_gate_reconstructions=0,opened_corners=0,
            weak_boundary_regularizations=0,residual_low_witnesses=0)
regularization_data=[]
for f in (Q(1653,400),Q(206625837,50000000)):
    M=high_regression_seed(f); s=extract(M)
    req(strict_r0(s) and is_macro_r22(s), 'Frozen witness qualifies')
    counts['high_seed_states']+=1
    for trans in (False,True):
        base=transpose(M) if trans else M
        bs=extract(base)
        for bits,N in gauges(base):
            ns=extract(N); complete_pivots(N)
            req(is_macro_r22(ns), 'Macro R and ranks preserved')
            req(ns['F']==f,'Orbit height preserved')
            req(left_gate(ns)==left_gate(bs),'Left invariants')
            req(right_gate(ns)==right_gate(bs),'Right invariants')
            req(any((all(a>0 for a in left_gate(ns)),all(a>0 for a in right_gate(ns)))),
                'At least one certified orbit gate')
            if all(a>0 for a in left_gate(ns)):
                P=canonical_from_left_gate(N)
            else:
                P=canonical_from_left_gate(transpose(N))
            complete_pivots(P)
            req(strict_r0(extract(P)), 'Exact canonical reconstruction')
            counts['explicit_gate_reconstructions']+=1
            counts['orbit_states']+=1
            NN=diagonal_contract(N,Q(1,10**8)); ss=extract(NN)
            complete_pivots(NN,strict_first_three=True)
            req(ss['F']==(1-Q(3,10**8))**2*f,'Exact contracted height')
            req(ss['F']>4 and is_macro_r22(ss),'High and macro preserved in regression')
            counts['strict_contractions']+=1
    N=diagonal_contract(M,Q(1,10**8))
    NN=open_last_corner(N,Q(1,10**8)); s2=extract(NN)
    req(s2['F']==extract(N)['F']-Q(1,10**8),'Opening height')
    req(s2['F']>4 and is_macro_r22(s2),'Noncorner R witness')
    req(flags(s2)['RL']==flags(extract(N))['RL'] and flags(s2)['RR']==flags(extract(N))['RR'],
        'R flags do not involve the opened w')
    counts['opened_corners']+=1

cases=[
    (Q(1,4),[Q(1,4),Q(1,4),Q(1,8)],[Q(1,8),Q(1,4),Q(1,2)]),
    (Q(1,4),[Q(0),Q(1,4),Q(1,8)],[Q(0),Q(1,4),Q(1,2)]),
    (Q(1,4),[Q(1,4),Q(0),Q(1,8)],[Q(1,8),Q(0),Q(1,2)]),
    (Q(0),[Q(1,4),Q(1,8),Q(0)],[Q(1,8),Q(1,4),Q(1,2)]),
    (Q(0),[Q(0),Q(0),Q(0)],[Q(1,8),Q(1,4),Q(1,2)]),
    (Q(1,4),[Q(1,4),Q(1,8),Q(1,8)],[Q(0),Q(1,4),Q(1,2)]),
]
for num,(be,u,x) in enumerate(cases,1):
    M=small_example(beta=be,u=u,x=x); s=extract(M)
    complete_pivots(M); req(weak_r0(s),'Weak ordered cone')
    req(any(a==0 for a in cofs_left(s)),'Actual cofactor boundary example')
    N=diagonal_contract(M,Q(1,100)); complete_pivots(N,strict_first_three=True)
    found=None
    for j in range(1,19):
        eps=Q(1,10**j)
        P=regularize_weak_receivers(N,eps)
        try:
            complete_pivots(P,strict_first_three=True)
            ps=extract(P)
            req(strict_r0(ps),'Strict R0 after regularization')
            req(all(abs(a)<1 for a in (ps['beta'],*ps['u'],*ps['x'])),'Strict receiver boxes')
            req(rank2(ps['u'],ps['x']),'Left rank created when needed')
        except AssertionError:
            continue
        found=(eps,P); break
    req(found is not None,'Finite replay regularization search')
    counts['weak_boundary_regularizations']+=1
    regularization_data.append({'case':num,'epsilon':str(found[0]),
                               'cofactors':[str(a) for a in cofs_left(extract(found[1]))]})

# A completely physical LOW-height obstruction to blind unconditional
# sign/transpose normalization. This is not a counterexample to alpha.
M=small_example(u=[Q(-1,4),Q(1,4),Q(1,10)],residual=True)
s=extract(M); complete_pivots(M,strict_first_three=True)
req(is_macro_r22(s) and is_generic(s),'Generic noncorner R22 residual witness')
req(residual_cell(s)==(1,1),'First-failure residual cell')
req(s['F']==Q(249,1000) and s['F']<4,'LOW-height scope')
for trans in (False,True):
    for _,N in gauges(transpose(M) if trans else M):
        req(not strict_r0(extract(N)),'No R0 image among the 16 permitted images')
counts['residual_low_witnesses']+=1
witness={'label':'LOW_HEIGHT_NORMALIZATION_OBSTRUCTION_NOT_ALPHA_COUNTEREXAMPLE',
         'F':str(s['F']),'M':[[str(a) for a in row] for row in M],
         'left_gate':[str(a) for a in left_gate(s)],
         'right_gate':[str(a) for a in right_gate(s)],'cell':[1,1]}
Path('low_residual_witness.json').write_text(json.dumps(witness,indent=2)+'\n')
Path('regularization_examples.json').write_text(json.dumps(regularization_data,indent=2)+'\n')
out={'status':'PASS','counts':counts,
     'scope':'finite dictionary and reconstruction checks; NO exclusion of F>alpha in the residual domain'}
Path('regression_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
