"""Exact core-changing, height-preserving transports for a complete two-step lift.

This is a transport/feasibility checker, NOT a whole-R height certificate.
Every half-plane comes from a specified actual physical band.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import gcd, lcm

def rat(x):
    if isinstance(x,(float,bool)): raise TypeError('Use exact integers or rational strings')
    return Q(x)

def native(M):
    M=[[rat(x) for x in row] for row in M]
    if len(M)!=5 or any(len(r)!=5 for r in M) or M[0][0]!=1: raise ValueError('Normalized 5x5 matrix required')
    e=-M[0][1];beta=M[1][0];p=M[1][1]+e*beta
    if p<=0: raise ValueError('Positive second pivot required')
    u=[M[i+2][0] for i in range(3)];v=M[0][2:]
    x=[(M[i+2][1]+e*u[i])/p for i in range(3)];q=[M[1][j+2]-beta*v[j] for j in range(3)]
    D=[[M[i+2][j+2]-u[i]*v[j]-x[i]*q[j] for j in range(3)] for i in range(3)]
    return dict(e=e,beta=beta,p=p,u=u,x=x,v=v,q=q,D=D,k=D[0][0])

def build(s):
    p,e,be=s['p'],s['e'],s['beta'];u,x,v,q,D=[s[n] for n in ['u','x','v','q','D']]
    return [[Q(1),-e,*v],[be,p-e*be,*[q[j]+be*v[j] for j in range(3)]]]+[
        [u[i],p*x[i]-e*u[i],*[D[i][j]+x[i]*q[j]+u[i]*v[j] for j in range(3)]] for i in range(3)]

def blocks(M):
    B=[[rat(a) for a in row] for row in M];out=[];pv=[]
    for st in range(5):
        if B[0][0]==0:raise ValueError('Zero pivot')
        if any(abs(z)>abs(B[0][0]) for row in B for z in row):raise ValueError('CP failure stage '+str(st+1))
        out.append(B);pv.append(B[0][0])
        if st<4:B=[[B[i][j]-B[i][0]*B[0][j]/B[0][0] for j in range(1,len(B))] for i in range(1,len(B))]
    return pv,out

def residual(s):
    D=s['D'];k=D[0][0]
    if k<=0:raise ValueError('Positive third pivot required')
    return [[D[i][j]-D[i][0]*D[0][j]/k for j in (1,2)] for i in (1,2)]

def physical_slacks(s):
    """All first/second stage bands, plus the complete third-pivot bands."""
    p,e,be=s['p'],s['e'],s['beta'];u,x,v,q,D=[s[n] for n in ['u','x','v','q','D']];k=D[0][0]
    rows=[]
    def band(z,b,label):rows.extend([(label+'+',b-z),(label+'-',b+z)])
    band(e,1,'e');band(be,1,'beta');band(p-e*be,1,'head')
    for i in range(3):
        band(u[i],1,'u'+str(i));band(x[i],1,'x'+str(i));band(v[i],1,'v'+str(i));band(q[i],p,'q'+str(i))
        band(p*x[i]-e*u[i],1,'L'+str(i));band(q[i]+be*v[i],1,'P'+str(i))
        for j in range(3):
            band(D[i][j],k,f'D{i}{j}');S=D[i][j]+x[i]*q[j]
            band(S,p,f'S{i}{j}');band(S+u[i]*v[j],1,f'O{i}{j}')
    return rows

def move(s, side, a, b):
    a,b=rat(a),rat(b);k=s['D'][0][0]
    if k<=0:raise ValueError('Positive source pivot required')
    z={key:([row[:] for row in val] if key=='D' else list(val) if isinstance(val,list) else val) for key,val in s.items()}
    D=s['D'];u,x,v,q=[s[n] for n in ['u','x','v','q']]
    if side=='left':
        ell=[D[i][0]/k for i in range(3)]
        z['u']=[u[i]+a*ell[i] for i in range(3)];z['x']=[x[i]+b*ell[i] for i in range(3)]
        z['D']=[[D[i][j]-ell[i]*(a*v[j]+b*q[j]) for j in range(3)] for i in range(3)]
    elif side=='right':
        rr=[D[0][j]/k for j in range(3)]
        z['v']=[v[j]+a*rr[j] for j in range(3)];z['q']=[q[j]+b*rr[j] for j in range(3)]
        z['D']=[[D[i][j]-(a*u[i]+b*x[i])*rr[j] for j in range(3)] for i in range(3)]
    else:raise ValueError('side must be left or right')
    z['k']=z['D'][0][0]
    return z

def halfplanes(s,side):
    """Rows (label,constant,coefficient_a,coefficient_b), all >=0.

    The affine character is proved symbolically in verify_identities.py.
    k>=k_source/2 prevents a zero pivot. It is inactive at the source and
    cannot be an active maximum certificate when the maximum >= k_source.
    """
    pp=[physical_slacks(move(s,side,a,b)) for a,b in [(0,0),(1,0),(0,1)]]
    rows=[]
    for (n,c),(n1,aa),(n2,bb) in zip(*pp):
        assert n==n1==n2
        ca,cb=aa-c,bb-c
        if ca==cb==0:
            if c<0:raise ValueError('Invalid fixed physical band: '+n)
            continue
        rows.append((n,c,ca,cb))
    if side=='left':da,db=-s['v'][0],-s['q'][0]
    else:da,db=-s['u'][0],-s['x'][0]
    rows.append(('positive_pivot_guard',s['k']/2,da,db))
    return rows

def normal_key(row):
    _,c,a,b=row;D=lcm(c.denominator,a.denominator,b.denominator)
    v=[int(x*D) for x in (c,a,b)];g=gcd(gcd(abs(v[0]),abs(v[1])),abs(v[2]))
    return tuple(t//g for t in v)

def vertices(rows):
    # Deduplicate positive multiples but keep a real physical source label.
    d={}
    for row in rows:d.setdefault(normal_key(row),row)
    rows=list(d.values());pts=set()
    for (n,c,a,b),(nn,C,A,B) in combinations(rows,2):
        det=a*B-A*b
        if not det:continue
        z=((b*C-B*c)/det,(A*c-a*C)/det)
        if all(cc+aa*z[0]+bb*z[1]>=0 for _,cc,aa,bb in rows):pts.add(z)
    if not pts:raise AssertionError('Source-containing compact transport polygon has no vertex')
    return sorted(pts)

def dual_at(rows,z,obj):
    """At most two active actual inequalities proving the global LP maximum."""
    active=[row for row in rows if row[1]+row[2]*z[0]+row[3]*z[1]==0]
    g,h=(-obj[0],-obj[1])
    for n,c,a,b in active:
        if a or b:
            v=g/a if a else h/b
            if v>=0 and v*a==g and v*b==h:return [(n,v)]
    for (n,c,a,b),(nn,C,A,B) in combinations(active,2):
        det=a*B-A*b
        if not det:continue
        v=(g*B-A*h)/det;w=(a*h-g*b)/det
        if v>=0 and w>=0:return [(n,v),(nn,w)]
    raise AssertionError('No exact two-row dual at claimed optimum')

def solve(M,side,target=Q(2)):
    M=[[rat(a) for a in row] for row in M]
    pv,_=blocks(M);s=native(M)
    if s['k']<=0:raise ValueError('Positive third pivot')
    rows=halfplanes(s,side);obj=(-s['v'][0],-s['q'][0]) if side=='left' else (-s['u'][0],-s['x'][0])
    vv=vertices(rows);z=max(vv,key=lambda z:(obj[0]*z[0]+obj[1]*z[1],z))
    cap=s['k']+obj[0]*z[0]+obj[1]*z[1]
    cert=dual_at(rows,z,obj)
    by={row[0]:row for row in rows}
    assert all(w>=0 for _,w in cert)
    assert sum(w*by[n][2] for n,w in cert)==-obj[0]
    assert sum(w*by[n][3] for n,w in cert)==-obj[1]
    assert cap==s['k']+sum(w*by[n][1] for n,w in cert)
    target=rat(target)
    if cap>=target>=s['k']:
        fac=(target-s['k'])/(cap-s['k']) if cap>s['k'] else Q(0)
        sel=(fac*z[0],fac*z[1]);status='TARGET_REACHED'
    else:sel=z;status='TARGET_NOT_REACHED' if cap<target else 'SOURCE_ABOVE_TARGET'
    ss=move(s,side,*sel);N=build(ss);npv,_=blocks(N)
    assert npv[:2]==pv[:2] and npv[3:]==pv[3:]
    assert residual(s)==residual(ss)
    assert [row[2:] for row in M[2:]]==[row[2:] for row in N[2:]]
    assert all(v>=0 for _,v in physical_slacks(ss))
    return dict(status=status,side=side,source_k=s['k'],max_k=cap,target=target,endpoint_k=ss['k'],parameters=sel,
                maximizing_parameters=z,dual=cert,vertex_count=len(vv),matrix=N,source_pivots=pv,endpoint_pivots=npv)

def merge_parallel(rows):
    """Keep the strongest inequality in each oriented normal direction."""
    found={}
    for row in rows:
        name,c,a,b=row
        den=lcm(a.denominator,b.denominator)
        ia,ib=int(a*den),int(b*den);g=gcd(abs(ia),abs(ib))
        if g==0:
            if c<0:raise ValueError('Contradictory constant')
            continue
        direction=(ia//g,ib//g);scale=Q(g,den)
        normc=c/scale
        if direction not in found or normc<found[direction][0]:found[direction]=(normc,row)
    return [v[1] for v in found.values()]

def small_rows(s,side):
    H=residual(s);r=H[0][0];w=H[1][1];k=s['k'];D=s['D']
    if H[0][1]!=r or H[1][0]!=r or not (0<k<=2 and r-w>4):raise ValueError('Small-pivot X-chart source required')
    a,b,c,d=-D[0][1]/k,-D[0][2]/k,D[1][0]/k,D[2][0]/k
    if not(0<b<a<=1 and 0<d<c<=1):raise ValueError('Use the A,B<0<c,d normalization')
    allrows=halfplanes(s,side)
    core={'D01-','D21+','D22-','D12+'} if side=='left' else {'D10+','D12+','D22-','D21+'}
    ordinary=[row for row in allrows if row[0]!='positive_pivot_guard' and not row[0].startswith('D')]
    ordinary=merge_parallel(ordinary)
    if len(ordinary)>6:raise AssertionError('Three-strip compression failure')
    selected=ordinary+[row for row in allrows if row[0] in core]
    if len(selected)>10:raise AssertionError('Ten physical rows maximum')
    selected += [row for row in allrows if row[0]=='positive_pivot_guard']
    da,db=(-s['v'][0],-s['q'][0]) if side=='left' else (-s['u'][0],-s['x'][0])
    selected.append(('pivot_cap_2',Q(2)-k,-da,-db))
    return selected

def solve_small(M,side):
    M=[[rat(a) for a in row] for row in M]
    pv,_=blocks(M);s=native(M);rows=small_rows(s,side)
    obj=(-s['v'][0],-s['q'][0]) if side=='left' else (-s['u'][0],-s['x'][0])
    pts=vertices(rows);z=max(pts,key=lambda v:(obj[0]*v[0]+obj[1]*v[1],v))
    cap=s['k']+obj[0]*z[0]+obj[1]*z[1];dual=dual_at(rows,z,obj)
    t=move(s,side,*z);N=build(t);npv,_=blocks(N)
    assert npv[:2]==pv[:2] and npv[3:]==pv[3:]
    assert all(val>=0 for _,val in physical_slacks(t))
    assert residual(t)==residual(s)
    if cap<2:
        assert all(n not in ('positive_pivot_guard','pivot_cap_2') for n,lam in dual)
    return dict(status='TARGET_REACHED' if cap==2 else 'TARGET_NOT_REACHED',side=side,source_k=s['k'],max_k=cap,
        parameters=z,dual=dual,vertex_count=len(pts),physical_row_count=len(rows)-2,matrix=N,source_pivots=pv,endpoint_pivots=npv)

def encode(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x

def verify_dual(M,side,proof):
    """Verify a submitted exact upper bound; does not trust search output."""
    blocks(M);s=native(M);rows=halfplanes(s,side);by={z[0]:z for z in rows}
    da,db=(-s['v'][0],-s['q'][0]) if side=='left' else (-s['u'][0],-s['x'][0])
    terms=[(name,rat(w)) for name,w in proof['dual']]
    if len(terms)>2 or any(w<0 for _,w in terms):raise ValueError('Invalid nonnegative two-row dual')
    if any(name not in by or name=='positive_pivot_guard' for name,w in terms):raise ValueError('Unknown or nonphysical band')
    if sum(w*by[name][2] for name,w in terms)!=-da or sum(w*by[name][3] for name,w in terms)!=-db:raise ValueError('Dual coefficient mismatch')
    bound=s['k']+sum(w*by[name][1] for name,w in terms)
    if bound!=rat(proof['max_k']):raise ValueError('Incorrect certified bound')
    if 'parameters' in proof:
        z=tuple(map(rat,proof['parameters']))
        if len(z)!=2:raise ValueError('Exactly two parameters required')
        t=move(s,side,*z)
        if not all(v>=0 for _,v in physical_slacks(t)) or t['k']!=bound:raise ValueError('Dual bound not attained by submitted endpoint')
        blocks(build(t))
    return bound
