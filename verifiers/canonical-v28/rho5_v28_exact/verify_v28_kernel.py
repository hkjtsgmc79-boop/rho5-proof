"""Exact arithmetic and majorant regression tests; not substitutes for coverage."""
from fractions import Fraction as Q
from pathlib import Path
import random,ctypes as C,sys,json
import verify_v28_coverage as v
BASE=Path(__file__).resolve().parent;S=v.S
v.LIB=v.build();rng=random.Random(280907)
lib=v.LIB;ptr=C.POINTER(C.c_int64)
lib.interval_arithmetic.argtypes=[C.c_int64]*4+[C.c_int,ptr]
arithmetic_count=0
for _ in range(1000):
    al,ah=sorted([rng.randint(-50*S,50*S) for _ in range(2)]);bl,bh=sorted([rng.randint(-50*S,50*S) for _ in range(2)])
    for op in range(3):
        z=(C.c_int64*2)();assert lib.interval_arithmetic(al,ah,bl,bh,op,z)==0
        if op==0:lo,hi=Q(al+bl,S),Q(ah+bh,S)
        elif op==1:lo,hi=Q(al-bh,S),Q(ah-bl,S)
        else:
            ps=[Q(a*b,S*S) for a in [al,ah] for b in [bl,bh]];lo,hi=min(ps),max(ps)
        assert Q(z[0],S)<=lo<=hi<=Q(z[1],S)
        assert 0<=lo-Q(z[0],S)<Q(1,S) and 0<=Q(z[1],S)-hi<Q(1,S)
        arithmetic_count+=1
sys.path.insert(0,str(BASE/'RHO5_V26_REBUILT'))
from localization_exact_core import guards_generic
cp=json.loads((BASE/'RHO5_V26_REBUILT/global_localization_partial_checkpoint.json').read_text())
boxes=[]
for front in cp['open_frontier'][:6]:boxes.append(([int(Q(x)*S) for x in front['lo']],[int(Q(x)*S) for x in front['hi']]))
boxes.append(([int(q*S) for q in v.QLO],[int(q*S)+1 for q in v.QHI]))
points=0;majorants=0
for lo,hi in boxes:
    bd,rows=v.evaluate(lo,hi,'MT');cen=[(l+h)//2 for l,h in zip(lo,hi)];rad=[max(h-c,c-l) for l,h,c in zip(lo,hi,cen)]
    for z in range(8):
        # Include non-dyadic rational points, so this is not restricted to grid values.
        pp=[Q(lo[i],S)+(Q(hi[i]-lo[i],S)*Q(rng.randint(0,13),13)) for i in range(6)]
        gs,g35,g36=guards_generic(pp,v.F);allg=gs+[g35,g36]
        for j,g in enumerate(allg):assert Q(bd[2*j],S)<=g<=Q(bd[2*j+1],S),(j,g)
        for jj,row in enumerate(rows):
            j=jj if jj<35 else jj-35 if jj<70 else 35
            aff=Q(row[0],S)+sum(Q(row[i+1],S)*(pp[i]-Q(cen[i],S))/Q(rad[i],S) for i in range(6) if rad[i])
            assert allg[j]<=aff,('majorant',j,jj);majorants+=1
        points+=1
print('V28_INTEGER_INTERVAL_KERNEL_TESTS_PASS',arithmetic_count,'arithmetic tests;',points,'rational points;',majorants,'affine-majorant checks')
