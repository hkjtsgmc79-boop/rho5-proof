"""Read-only proof acceptance. Uses integer intervals and Fraction only.

No numerical optimizer is imported. Linear multipliers are treated as untrusted
proof suggestions; their exact weighted contradiction is independently checked.
"""
from __future__ import annotations
import ctypes, json, sys, time
from pathlib import Path
from fractions import Fraction

ROOT=Path(__file__).resolve().parent
SCALE=1<<32

def replay(key: str, proof: Path|None=None, verbose: bool=True):
    sp=json.loads((ROOT/'certificates'/f'{key}.json').read_text())
    n=len(sp['variables'])
    lib=ctypes.CDLL(str(ROOT/f'linear_{key}.so'))
    lib.assess.argtypes=[ctypes.POINTER(ctypes.c_longlong)]*3
    lib.assess.restype=ctypes.c_int
    m=lib.nr()
    assert lib.nv()==n and m==sum(2 if eq else 1 for _,eq,_ in sp['roots'])
    box_type=ctypes.c_longlong*(2*n);rad_type=ctypes.c_longlong*n
    coeff_type=ctypes.c_longlong*(m*(n+1))
    todo=[(sp['root_box'],0)]
    nodes=interval_leaves=farkas_leaves=maximum_depth=0
    min_separation=None
    start=time.time()
    with (proof or ROOT/'certificates'/f'{key}.lp_proof').open() as stream:
        assert stream.readline().strip()=='V24-EXACT-MEAN-FARKAS-1 32', 'wrong format'
        while todo:
            box,depth=todo.pop();maximum_depth=max(maximum_depth,depth);nodes+=1
            raw=box_type(*[v for pair in box for v in pair]);radius=rad_type();coeff=coeff_type()
            status=lib.assess(raw,radius,coeff)
            assert status>=0,'interval kernel error'
            words=stream.readline().split();assert words,'truncated proof'
            tag=words[0]
            if tag=='L':
                assert len(words)==1 and status==1,'false interval contradiction'
                interval_leaves+=1
            elif tag=='F':
                assert status==0,'linearization unavailable'
                length=int(words[1]);assert 1<=length<=m
                assert len(words)==2+2*length,'invalid cut length'
                indices=[int(words[2+2*j])for j in range(length)]
                multipliers=[int(words[3+2*j])for j in range(length)]
                assert indices==sorted(set(indices)) and 0<=indices[0] and indices[-1]<m
                assert all(w>0 for w in multipliers),'nonpositive multiplier'
                aggregate=[Fraction(0)for _ in range(n)]
                constant=Fraction(0)
                for row,w in zip(indices,multipliers):
                    a=[int(coeff[row*(n+1)+i])*int(radius[i])for i in range(n)]
                    b=int(coeff[row*(n+1)+n])*SCALE
                    den=max(abs(b),max(map(abs,a))) or 1
                    multiplier=Fraction(w,den)
                    constant+=multiplier*b
                    for i in range(n):aggregate[i]+=multiplier*a[i]
                # Necessary affine rows must all be >=0; their positive sum
                # cannot be <0 at every point of the enclosing [-1,1]^n cube.
                upper=constant+sum((abs(a)for a in aggregate),Fraction(0))
                assert upper<0, 'Farkas row has no strict exact contradiction'
                separation=-upper
                min_separation=separation if min_separation is None else min(min_separation,separation)
                farkas_leaves+=1
            elif tag=='B':
                assert status in (0,2) and len(words)==3,'invalid branch'
                index=int(words[1]);cut=int(words[2]);assert 0<=index<8
                box=[[int(raw[2*i]),int(raw[2*i+1])]for i in range(n)]
                assert box[index][0]<cut<box[index][1],'non-interior split'
                right=[pair[:]for pair in box]
                box[index][1]=cut;right[index][0]=cut
                todo.append((right,depth+1));todo.append((box,depth+1))
            else:raise AssertionError('unknown or unfinished proof node: '+tag)
            if verbose and nodes%10000==0:
                print(key,'accepted nodes',nodes, 'seconds',round(time.time()-start,2),flush=True)
        assert stream.readline().strip()=='END','missing final marker'
        assert not stream.read().strip(),'unconsumed proof data'
    leaves=interval_leaves+farkas_leaves
    assert nodes==2*leaves-1
    result=dict(key=key,nodes=nodes,leaves=leaves,interval_leaves=interval_leaves,
                farkas_leaves=farkas_leaves,max_depth=maximum_depth,
                min_exact_farkas_separation=str(min_separation),seconds=time.time()-start)
    if verbose:print('EXACT ACCEPTANCE PASS',json.dumps(result),flush=True)
    return result

if __name__=='__main__':
    result=replay(sys.argv[1],Path(sys.argv[2])if len(sys.argv)>2 else None)
    if len(sys.argv)==2:(ROOT/f'{sys.argv[1]}_acceptance.json').write_text(json.dumps(result,indent=2)+'\n')
