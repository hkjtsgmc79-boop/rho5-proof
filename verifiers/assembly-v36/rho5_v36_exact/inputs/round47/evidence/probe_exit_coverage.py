#!/usr/bin/env python3
"""Bounded diagnosis: find full physical sources outside the six frozen A exits.

Newton proposes coordinates only. A candidate is retained only after independent
Fraction full-matrix CP, semantic rows, root membership and alpha comparisons.
This script never edits models, proof rules, or search checkpoints.
"""
from pathlib import Path
from fractions import Fraction as Q
import sys, json, argparse, time, hashlib
import mpmath as mp

ap=argparse.ArgumentParser()
ap.add_argument('--package',type=Path,required=True)
ap.add_argument('--out',type=Path,required=True)
a=ap.parse_args();root=a.package.resolve();sys.path.insert(0,str(root))
from local_model import source, diff, NAMES
from native import to_matrix, verify_matrix, gates
from alpha_ports import proves

mp.mp.dps=90
cert=json.loads((root/'local_wall_certificate.json').read_text())
model=json.loads((root/'models/II_LOW_ALPHA/model.json').read_text())
alpha=json.loads((root/'alpha.json').read_text())
al=Q(alpha['isolating_interval']['lower']);au=Q(alpha['isolating_interval']['upper'])
gamma=Q(model['target']);case=cert['cases'][1]
cen=list(map(Q,case['center']));cols=[i for i in range(22) if i!=7]
polys=source();selected=[polys[n] for n in case['active_labels']]
jpolys=[[diff(poly,i) for i in cols] for poly in selected]
delta_index=case['active_labels'].index('r+w')

def mq(q):
    q=Q(q);return mp.mpf(q.numerator)/q.denominator

def meval(poly,z):
    out=mp.mpf(0)
    for mon,c in poly.items():
        t=mq(c)
        for i in mon:t*=z[i]
        out+=t
    return out

def propose(p,delta):
    z=list(map(mq,cen));z[7]=mq(p)
    for it in range(15):
        f=mp.matrix([meval(poly,z)-(mq(delta) if j==delta_index else 0)
                     for j,poly in enumerate(selected)])
        if mp.norm(f,mp.inf)<mp.mpf('1e-75'):break
        jac=mp.matrix([[meval(poly,z) for poly in row] for row in jpolys])
        step=mp.lu_solve(jac,f)
        for j,i in enumerate(cols):z[i]-=step[j]
    else:raise ValueError('Newton did not converge')
    # All nonlinear contacts are merely proposals; rounding and strictification
    # do not receive any credit until verify_matrix independently accepts M.
    z=[Q(mp.nstr(x,72)) for x in z]
    eta=Q(1,10**50);h=[Q(1),1-eta,1-2*eta,1-3*eta,1-3*eta]
    M=to_matrix(z)
    M=[[h[i]*h[j]*M[i][j] for j in range(5)] for i in range(5)]
    return M

def check(M,p,delta):
    ans=verify_matrix(M);z=ans['point'];F=ans['F'];zz=z+[z[8]*z[10]]
    assert ans['strict_first_three'] and gamma<F<al<au<2*z[1]
    assert Q(model['K'])<z[0]<Q(model['J']) and z[1]<z[0] and -z[1]<z[2]<z[1]
    den=Q(model['root_denominator'])
    assert all(Q(l)/den<=v<=Q(u)/den for l,u,v in zip(*model['root_numerators'],zz))
    vals=zz+[zz[i]*zz[j] for i,j in model['pairs']]
    margins=[Q(row['rhs'])-sum((Q(c)*v for c,v in zip(row['coefficients'],vals)),Q(0)) for row in model['rows']]
    assert all(m>=0 for m in margins), 'necessary row rejected'
    safe=[i for i in range(6) if proves([(x,x) for x in zz],i,cert)]
    distances=[max(abs(x-Q(c)) for x,c in zip(z,item['center'])) for item in cert['cases']]
    gl,gr=gates(z)
    return {'status':'EXACT_PHYSICAL_SOURCE_OUTSIDE_ALL_SIX_A_EXITS' if not safe else 'EXACT_PHYSICAL_SOURCE_WITH_FROZEN_A_EXIT',
            'matrix':[[str(x) for x in row] for row in M], 'point':list(map(str,z)),
            'p_proposal':str(p),'delta_proposal':str(delta),'F':str(F),
            'gamma_gap':str(F-gamma),'alpha_lower_gap':str(al-F),
            'two_r_minus_alpha_upper':str(2*z[1]-au),'r_plus_w':str(z[1]+z[2]),
            'safe_codes':safe,'distances_to_centers':list(map(str,distances)),
            'minimum_necessary_margin':str(min(margins)),'necessary_rows':len(margins),
            'strict_first_three':True,'actual_native_roundtrip':True,
            'left_gate':all(x>0 for x in gl),'right_gate':all(x>0 for x in gr),
            'display':{'p':float(z[7]),'F':float(F),'gamma_gap':float(F-gamma),
                       'alpha_gap':float(al-F),'two_r_minus_alpha':float(2*z[1]-au),
                       'closest_center_distance':float(min(distances))}}

start=time.monotonic();records=[];trials=[]
# A small, fixed probe grid, never an unbounded optimization campaign.
for offset in ('0.00008','-0.00008','0.00016','-0.00016','0.00032','-0.00032','0.00064','-0.00064'):
    for delta in ('0.0000001','0.00000015','0.0000002'):
        p=cen[7]+Q(offset)
        try:
            M=propose(p,Q(delta));rec=check(M,p,Q(delta));records.append(rec)
            trials.append({'offset':offset,'delta':delta,'status':rec['status'],'display':rec['display']})
        except Exception as e:
            trials.append({'offset':offset,'delta':delta,'status':'NO_ACCEPTED_CONTROL','reason':type(e).__name__+': '+str(e)})
        print(json.dumps(trials[-1]),flush=True)
result={'status':'BOUNDED_EXACT_EXIT_COVERAGE_DIAGNOSTIC','seconds':time.monotonic()-start,
        'alpha_counterexample':False,'trials':trials,'records':records,
        'outside_all_A_count':sum(not r['safe_codes'] for r in records),
        'model_sha256':hashlib.sha256((root/'models/II_LOW_ALPHA/model.json').read_bytes()).hexdigest(),
        'certificate_sha256':hashlib.sha256((root/'local_wall_certificate.json').read_bytes()).hexdigest(),
        'no_tree_or_model_mutations':True}
a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('records','trials')}),flush=True)
