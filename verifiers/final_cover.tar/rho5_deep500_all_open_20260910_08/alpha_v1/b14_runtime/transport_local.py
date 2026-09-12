"""Exact conditional B-to-X enclosure; V43 theorem is a frozen dependency.
No claim that an arbitrary box is physically populated. Sort branches cover
closed s>=t and s<=t, including their common wall. Coefficient dependencies
are conservatively retained through rational interval arithmetic.
"""
from fractions import Fraction as Q
from exact_interval import I,serial
import structural_rules as sr
KAPPA=[Q(13,4),Q(21),Q(28),Q(26)]
XORDER='k r w A B c d p e beta u0 u1 u2 x0 x1 x2 v0 v1 v2 q0 q1 q2'.split()
def positive_part_bound(a):
    if a.hi<0:raise ValueError('physically impossible gap branch')
    return I(max(Q(0),a.lo),a.hi)
def sorted_R(x):
    r,s,t=x['r'],x['s'],x['t']
    if r.lo<=0 or x['p'].lo<=0 or x['k'].lo<=0:raise ValueError('positive pivot required')
    g=positive_part_bound(r-s);h=positive_part_bound(s-t)
    Z=2*r+t-s
    if Z.lo<=0 or (r+s).lo<=0:raise ValueError('transport denominator not certified positive')
    mu=g/Z;lam=1-mu;nu=g*lam/(r+s);xi=1-nu
    R=r-g*lam
    delta=2*R*h/(r+s)
    ell=g*delta/(2*r)
    # On physical ordered inputs R,delta,ell nonnegative. Intersection is valid.
    R=positive_part_bound(R);delta=positive_part_bound(delta);ell=positive_part_bound(ell)
    y=x.copy();y['r']=R;y['w']=-R+delta
    for ww in ('u','x'):
        y[ww+'1']=lam*x[ww+'1']-mu*x[ww+'2']
        y[ww+'2']=-nu*x[ww+'1']-xi*x[ww+'2']
    y['c']=lam*x['c']-mu*x['d'];y['d']=-nu*x['c']-xi*x['d']
    y['A'],y['B']=x['B'],x['A']
    for ww in ('v','q'):y[ww+'1'],y[ww+'2']=x[ww+'2'],x[ww+'1']
    return [y[n] for n in XORDER],ell,{'g':g,'h':h,'Z':Z,'mu':mu,'lambda':lam,'nu':nu,'xi':xi,'delta':delta}
def sorted_branches(y):
    # Whenever the interval order is certified, use one branch only.
    if y['s'].lo>=y['t'].hi:return [('S_GE_T',y)]
    if y['t'].lo>=y['s'].hi:return [('S_LE_T',sr.diagonal_swap(y))]
    return [('S_GE_T',y),('S_LE_T',sr.diagonal_swap(y))]
def local_candidates(x,centers):
    results=[]
    for rep,y in sr.representations(x):
        bs=[]
        for branch,z in sorted_branches(y):
            target,ell,co=sorted_R(z)
            ds=[max(max(abs(v.lo-c),abs(v.hi-c))for v,c in zip(target,cen[:22]))for cen in centers]
            scores=[dist+KAPPA[j]*ell.hi for j,dist in enumerate(ds)]
            j=min(range(4),key=lambda j:scores[j])
            bs.append({'branch':branch,'center':j,'distance':ds[j],'loss_upper':ell.hi,'budget':scores[j],'target':target,'coefficients':co,'status':'ALPHA_SAFE'if scores[j]<=Q(3,1000)else'OPEN_HEIGHT'})
        results.append({'rep':rep,'status':'ALPHA_SAFE'if all(b['status']=='ALPHA_SAFE'for b in bs)else'OPEN_HEIGHT','branches':bs,'max_budget':max(b['budget']for b in bs)})
    return results
