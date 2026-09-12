"""Independent Fraction interval oracle on actual native tail packets.

The standalone interval determinant criterion is iff for an isolated 2x2
rank-one completion. When used inside the full X model it is NECESSARY only:
head/prefix/global factor constraints have not been eliminated by it.
"""
from fractions import Fraction as Q
from itertools import product

def add(a,b):return a[0]+b[0],a[1]+b[1]
def sub(a,b):return a[0]-b[1],a[1]-b[0]
def meet(a,b):return max(a[0],b[0]),min(a[1],b[1])
def empty(a):return a[0]>a[1]
def mul(a,b):
 vals=[x*y for x in a for y in b];return min(vals),max(vals)
def impossible(z):
 if any(empty(a) for a in z):return True
 a,b=mul(z[0],z[3]),mul(z[1],z[2]);return a[1]<b[0] or b[1]<a[0]

def exclusion(lo,hi):
    vals=list(zip(map(Q,lo),map(Q,hi)));p,k=vals[7][1],vals[0][1]
    if p<0 or k<0:raise ValueError('positive p,k upper bounds required')
    pb,kb,one=(-p,p),(-k,k),(Q(-1),Q(1))
    h=[];core=[];stage=[];orig=[]
    for i,j in product((1,2),repeat=2):
        h.append(vals[2 if i==j==2 else 1])
        core.append(meet(mul(vals[4+i],vals[2+j]),kb))
        stage.append(meet(mul(vals[13+i],vals[19+j]),pb))
        orig.append(meet(mul(vals[10+i],vals[16+j]),one))
    for _ in range(2):
        for n in range(4):
            d=meet(add(h[n],core[n]),kb)
            s=meet(add(d,stage[n]),pb)
            o=meet(add(s,orig[n]),one)
            if any(map(empty,[core[n],stage[n],orig[n],d,s,o])):return 3
            orig[n]=meet(orig[n],sub(o,s));s=meet(s,sub(o,orig[n]))
            stage[n]=meet(stage[n],sub(s,d));d=meet(d,sub(s,stage[n]))
            core[n]=meet(core[n],sub(d,h[n]))
            if any(map(empty,[core[n],stage[n],orig[n],d,s])):return 3
        for code,z in enumerate((stage,orig,core)):
            if impossible(z):return code
    return -1

def stage_tail_intervals(D,p):
    """Necessary and sufficient for the ISOLATED free stage-tail problem."""
    p=Q(p)
    if p<0:raise ValueError('p must be nonnegative')
    return [meet((-p,p),(-p-Q(d),p-Q(d))) for d in D]
