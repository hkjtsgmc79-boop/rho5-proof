"""Same-source core-head scaling, with exact maximal third pivot.

All receiver vectors and the 2x2 Schur tail remain fixed. The original/stage
3x3 blocks do NOT remain fixed: their head row and column are checked explicitly.
No height theorem or unproved safety label is built into the transformation.
"""
from __future__ import annotations
from fractions import Fraction as Q
from copy import deepcopy
from native_checker import build,physical_slacks,residual,blocks,rat

def validate(s):
    if s['p']<=0 or s['D'][0][0]<=0:raise ValueError('positive p and k required')
    for name,value in physical_slacks(s):
        if value<0:raise ValueError('not physical: '+name)
    blocks(build(s))

def ceilings(s):
    """None means an unbounded arm scale, never a zero denominator."""
    validate(s)
    D,p,u,x,v,q=s['D'],s['p'],s['u'],s['x'],s['v'],s['q'];k=D[0][0]
    corner=[('S00+',p-x[0]*q[0]),('O00+',1-x[0]*q[0]-u[0]*v[0])]
    row=[];col=[]
    for dst,cells in [(row,[(0,j) for j in (1,2)]),(col,[(i,0) for i in (1,2)])]:
        for i,j in cells:
            a=D[i][j]
            if not a:continue
            eps=1 if a>0 else -1
            for layer,h,shift in [('S',p,x[i]*q[j]),('O',Q(1),x[i]*q[j]+u[i]*v[j])]:
                C=h-eps*shift
                assert C>=abs(a)>0
                dst.append({'label':f'{layer}{i}{j}'+('+' if eps==1 else '-'),
                            'capacity':C,'scale':C/abs(a),'i':i,'j':j,'sign':eps})
    amax=min((r['scale'] for r in row),default=None)
    bmax=min((r['scale'] for r in col),default=None)
    h00=min(v for _,v in corner)
    arms=None if amax is None or bmax is None else k*amax*bmax
    cap=h00 if arms is None else min(h00,arms)
    assert cap>=k
    return {'k':k,'corner':corner,'row':row,'col':col,'amax':amax,'bmax':bmax,'corner_cap':h00,'arm_cap':arms,'kmax':cap}

def move(s,a,b,check=True):
    a,b=rat(a),rat(b)
    if a<1 or b<1:raise ValueError('the certified monotone construction needs a,b>=1')
    z=deepcopy(s);D=z['D'];D[0][0]*=a*b
    for j in (1,2):D[0][j]*=a
    for i in (1,2):D[i][0]*=b
    z['k']=D[0][0]
    if check:
        validate(z)
        assert residual(s)==residual(z)
        for key in ['p','e','beta','u','x','v','q']:assert z[key]==s[key]
        assert blocks(build(s))[0][3:]==blocks(build(z))[0][3:]
    return z

def reach(s,target):
    target=rat(target);data=ceilings(s);k=data['k']
    if not k<=target<=data['kmax']:raise ValueError('target outside exact attainable interval')
    product=target/k
    a=product if data['amax'] is None else min(product,data['amax'])
    b=product/a
    assert a>=1 and b>=1
    z=move(s,a,b)
    assert z['k']==target
    return z,{'row_scale':a,'column_scale':b,'target':target}

def boundary_labels(s,z):
    """At maximal k, either the corner cap or one row and one column are active."""
    caps=ceilings(s);assert z['k']==caps['kmax']
    sl=dict(physical_slacks(z))
    corner=[name for name,_ in caps['corner'] if sl[name]==0]
    row=[d['label'] for d in caps['row'] if sl[d['label']]==0]
    col=[d['label'] for d in caps['col'] if sl[d['label']]==0]
    if not corner and not(row and col):raise AssertionError('maximality contact lost')
    return {'corner':corner,'row':row,'column':col}

if __name__=='__main__':
    import json,sys
    from native_checker import native
    obj=json.load(open(sys.argv[1]));s=native(obj.get('M',obj));z,params=reach(s,sys.argv[2])
    print(json.dumps({'M':build(z),'parameters':params},default=str,indent=2))
