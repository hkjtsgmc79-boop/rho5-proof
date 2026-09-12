#!/usr/bin/env python3
"""Exact six-variable elimination on the complete normalized negative-D fibre.
Input frame order: k,A,B,c,d,u[3],x[3],v[3],q[3] (17 real coordinates).
The algorithm uses Fraction only. 'COMPLETE' is feasibility/maximality of one
fixed frame, NOT a global alpha bound. All q coordinates are actual q, not q/p.
"""
from __future__ import annotations
from fractions import Fraction as Q
from typing import Any, Mapping, Sequence
from pathlib import Path
import json, sys

FRAME_NAMES = ('k','A','B','c','d') + tuple(f'{a}{i}' for a in ('u','x','v','q') for i in range(3))
GAP_NAMES = ('k','r','w','A','B','c','d','p','e','beta') + tuple(f'{a}{i}' for a in ('u','x','v','q') for i in range(3)) + ('sigma','tau')

def rational(x: Any) -> Q:
    if isinstance(x, bool) or isinstance(x, float):
        raise TypeError('Use exact integers or fraction/decimal strings, never floats/bools')
    if isinstance(x, (int,str,Q)): return Q(x)
    raise TypeError(f'Unsupported rational value: {type(x).__name__}')

def frame_values(frame: Sequence[Any] | Mapping[str,Any]) -> list[Q]:
    if isinstance(frame, Mapping):
        if 'frame' in frame: return frame_values(frame['frame'])
        if all(n in frame for n in FRAME_NAMES): return [rational(frame[n]) for n in FRAME_NAMES]
        if all(n in frame for n in ('k','A','B','c','d','u','x','v','q')):
            
            if any(not isinstance(frame[a],(list,tuple)) or len(frame[a])!=3 for a in ('u','x','v','q')):
                raise ValueError('Each receiver must have exactly three coordinates')
            return [rational(frame[n]) for n in FRAME_NAMES[:5]] + [rational(v) for a in ('u','x','v','q') for v in frame[a]]
        raise ValueError('Unknown frame schema')
    values=list(frame)
    if len(values)!=17: raise ValueError('Exactly 17 frame coordinates required')
    return list(map(rational,values))

def extract_frame(gap: Sequence[Any]) -> list[Q]:
    z=list(map(rational,gap))
    if len(z)!=24 or z[2]!=-z[1]: raise ValueError('Expected 24-coordinate negative-D gap source')
    return [z[i] for i in (0,3,4,5,6)]+z[10:22]

def beta_interval(v: Sequence[Q], q: Sequence[Q]):
    low, high=Q(0),Q(1); sources=[]
    for j,(vj,qj) in enumerate(zip(v,q)):
        if not vj:
            if abs(qj)>1: return None
            continue
        a,b=sorted(((-1-qj)/vj,(1-qj)/vj))
        low=max(low,a); high=min(high,b)
        sources.append({'j':j,'lower':a,'upper':b})
    return (low,high,sources) if low<=high else None

def prefix_capacity(u: Sequence[Q],x: Sequence[Q],beta: Q):
    """Maximum p>=1 over e in [0,1]. At most six positive rational caps.
    The opposite side of each L strip is automatic since |u|<=1.
    beta=0 is handled separately, with p=1,e=0.
    """
    if not 0<=beta<=1: raise ValueError('beta outside [0,1]')
    if any(abs(y)>1 for y in list(u)+list(x)): raise ValueError('receiver bound')
    if beta==0: return Q(1),Q(0),[{'kind':'zero_beta','value':Q(1)}]
    rows=[('head',Q(1),beta)]
    for i,(ui,xi) in enumerate(zip(u,x)):
        if xi: rows.append((f'L{i}',abs(xi),ui if xi>0 else -ui))
    caps=[]
    for name,a,b in rows:
        if b>=0:
            caps.append({'kind':'upper_e' if b>0 else 'zero_slope','row':name,'value':(1+b)/a})
    for ni,ai,bi in rows:
        if bi<=0: continue
        for nj,aj,bj in rows:
            if bj>=0: continue
            den=aj*bi-ai*bj
            assert den>0
            caps.append({'kind':'opposite_slopes','rows':[ni,nj], 'value':(bi-bj)/den})
    assert 1<=len(caps)<=6
    p=min(z['value']for z in caps)
    e=max([Q(0)]+[(a*p-1)/b for _,a,b in rows if b>0])
    assert 1<=p<=2 and 0<=e<=1
    assert p-beta*e<=1
    assert all(abs(p*xi-e*ui)<=1 for xi,ui in zip(x,u))
    return p,e,caps

def matrices(z: Sequence[Any]):
    z=list(map(rational,z))
    if len(z)!=24: raise ValueError('Expected gap coordinates')
    k,r,w,A,B,c,d,p,e,beta=z[:10]
    u,x,v,q=z[10:13],z[13:16],z[16:19],z[19:22]
    s,t=r-z[22],r-z[23]
    D=[[k,A,B],[c*k,r+c*A,s+c*B],[d*k,t+d*A,w+d*B]]
    S=[[D[i][j]+x[i]*q[j]for j in range(3)]for i in range(3)]
    O=[[S[i][j]+u[i]*v[j]for j in range(3)]for i in range(3)]
    M=[[Q(1),-e]+v,[beta,p-e*beta]+[q[j]+beta*v[j]for j in range(3)]]
    M += [[u[i],p*x[i]-e*u[i]]+O[i]for i in range(3)]
    return M,D,S,O

def check_complete(z: Sequence[Any]):
    z=list(map(rational,z)); M,D,S,O=matrices(z)
    k,r,w,A,B,c,d,p,e,beta=z[:10]
    u,x,v,q=z[10:13],z[13:16],z[16:19],z[19:22]
    s,t=r-z[22],r-z[23]
    assert k>0 and p>0 and r>0 and 0<=s<=r and 0<=t<=r and abs(w)<=r
    assert all(abs(a)<=1 for a in [e,beta,p-e*beta]+u+x+v)
    assert all(abs(a)<=p for a in q)
    assert all(abs(p*x[i]-e*u[i])<=1 for i in range(3))
    assert all(abs(q[j]+beta*v[j])<=1 for j in range(3))
    for T,h in ((D,k),(S,p),(O,Q(1))): assert all(abs(a)<=h for row in T for a in row)
    W=M; pivots=[]
    for step in range(5):
        pivot=W[0][0]; pivots.append(pivot)
        assert pivot!=0 and all(abs(a)<=abs(pivot)for row in W for a in row)
        W=[[W[i][j]-W[i][0]*W[0][j]/pivot for j in range(1,len(W))]for i in range(1,len(W))]
    F=s*t/r-w
    assert pivots==[Q(1),p,k,r,-F]
    return {'matrix':M,'D':D,'S':S,'O':O,'pivots':pivots,'F':F}

def capacity(frame: Sequence[Any] | Mapping[str,Any]) -> dict[str,Any]:
    f=frame_values(frame); k,A,B,c,d=f[:5];u,x,v,q=[f[a:a+3]for a in (5,8,11,14)]
    def empty(reason: str, **kw): return {'status':'EMPTY_PREFIX_TAIL_FIBRE', 'reason':reason,**kw}
    if k<=0: return empty('nonpositive_k')
    if any(abs(y)>1 for y in u+x+v):return empty('receiver_box')
    if abs(A)>k or abs(B)>k or abs(c)>1 or abs(d)>1:return empty('fixed_core_head')
    bi=beta_interval(v,q)
    if bi is None:return empty('right_prefix_interval')
    beta=bi[1]
    p,e,pcaps=prefix_capacity(u,x,beta)
    if any(abs(y)>p for y in q): return empty('q_stage_bound',prefix_p=p)
    fixed={(0,0):k,(0,1):A,(0,2):B,(1,0):c*k,(2,0):d*k}
    for (i,j),a in fixed.items():
        if abs(a+x[i]*q[j])>p:return empty(f'fixed_S{i}{j}',prefix_p=p)
        if abs(a+x[i]*q[j]+u[i]*v[j])>1:return empty(f'fixed_O{i}{j}')
    low={};up={};providersL={};providersU={}
    for i in (1,2):
        for j in (1,2):
            lows=[-k,-p-x[i]*q[j],-1-x[i]*q[j]-u[i]*v[j]]
            ups=[k,p-x[i]*q[j],1-x[i]*q[j]-u[i]*v[j]]
            low[i,j]=max(lows);up[i,j]=min(ups)
            providersL[i,j]=[a for a,y in zip('DSO',lows)if y==low[i,j]]
            providersU[i,j]=[a for a,y in zip('DSO',ups)if y==up[i,j]]
    rl=max(Q(0),low[1,1]-c*A,d*B-up[2,2]);R=min(up[1,1]-c*A,d*B-low[2,2])
    sl=max(Q(0),low[1,2]-c*B);su=up[1,2]-c*B
    tl=max(Q(0),low[2,1]-d*A);tu=up[2,1]-d*A
    S=min(R,su);T=min(R,tu)
    if R<=0 or R<rl or S<sl or T<tl:return empty('tail_interval', r_bounds=[rl,R],s_bounds=[sl,su],t_bounds=[tl,tu])
    z=[k,R,-R,A,B,c,d,p,e,beta]+u+x+v+q+[R-S,R-T]
    checked=check_complete(z)
    rs=[]
    if R==up[1,1]-c*A:rs.extend(a+'11+'for a in providersU[1,1])
    if R==d*B-low[2,2]:rs.extend(a+'22-'for a in providersL[2,2])
    return {'status':'COMPLETE_FIXED_FRAME_MAXIMUM', 'frame':f, 'prefix':{'beta_interval':bi[:2], 'beta':beta,'p':p,'e':e, 'caps':pcaps},
            'tail':{'r':R,'s':S,'t':T,'F':checked['F'],'r_bounds':[rl,R],'s_bounds':[sl,su],'t_bounds':[tl,tu]},
            'point_gap':z,'matrix':checked['matrix'],'pivots':checked['pivots'],
            'contacts':{'r':rs,'s':['s=r']if S==R else[a+'12+'for a in providersU[1,2]], 't':['t=r']if T==R else[a+'21+'for a in providersU[2,1]]},
            'safe_face':S==R or T==R, 'global_alpha_bound_claimed':False}

def encode(obj):
    if isinstance(obj,Q):return str(obj)
    if isinstance(obj,dict):return {k:encode(v)for k,v in obj.items()}
    if isinstance(obj,(list,tuple)):return [encode(v)for v in obj]
    return obj

def main():
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input');ap.add_argument('--output');a=ap.parse_args()
    try:result=encode(capacity(json.loads(Path(a.input).read_text(encoding='utf-8'))))
    except (ValueError,TypeError,KeyError,AssertionError)as err:
        print(json.dumps({'status':'INVALID_INPUT_OR_FAILED_CHECK','error':str(err)}));return 2
    text=json.dumps(result,ensure_ascii=False,indent=2)+'\n'
    if a.output:Path(a.output).write_text(text,encoding='utf-8')
    else:print(text,end='')
    return 0
if __name__=='__main__':sys.exit(main())
