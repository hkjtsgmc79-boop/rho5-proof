import json
from fractions import Fraction as Q
from pathlib import Path
from localization_exact_core import exact_rows, combo_margin
BASE=Path(__file__).resolve().parent
D=json.loads((BASE/'upper_tree_recovered.json').read_text())
f=Q(103313,25000)
rootlo=[Q(617,1000),Q(7788,10000),Q(4525,10000),Q(97352,100000),Q(99998,100000),Q(1944,10000)]
roothi=[Q(6181,10000),Q(7795,10000),Q(454,1000),Q(97361,100000),Q(1),Q(19501,100000)]
widths=[roothi[i]-rootlo[i] for i in range(6)]
leaves={int(x['node']):x for x in D['leaves']}
visited=set(); exact_margins=[]

def qv(s): return Q(s)
def rec(lo,hi,depth,nid):
    if nid in leaves:
        L=leaves[nid]; visited.add(nid)
        assert depth==int(L['depth'])
        assert lo==[qv(x) for x in L['lo']]
        assert hi==[qv(x) for x in L['hi']]
        assert L['kind']=='combo'
        direct,rows=exact_rows(lo,hi,f)
        assert direct is None, 'regenerated tree leaf unexpectedly has direct interval contradiction'
        weights=[(int(j),int(w)) for j,w in L['weights']]
        assert all(w>=0 for _,w in weights)
        m=combo_margin(weights,rows)
        assert m<0, (nid,m)
        exact_margins.append(m)
        return 1
    dim=max(range(6), key=lambda i: Q(hi[i]-lo[i], widths[i]) if widths[i] else Q(-1))
    mid=(lo[dim]+hi[dim])/2
    llo=list(lo); lhi=list(hi); lhi[dim]=mid
    rlo=list(lo); rhi=list(hi); rlo[dim]=mid
    return 1+rec(llo,lhi,depth+1,nid*2)+rec(rlo,rhi,depth+1,nid*2+1)

nodes=rec(rootlo,roothi,0,1)
assert visited==set(leaves)
assert nodes==int(D['nodes'])==169
assert len(leaves)==85
assert D['stats']=={'interval':0,'combo':85,'inside':0,'open':0}
print('V26_REGENERATED_FPLUS_UPPER_TREE_EXACT_REPLAY_PASSED')
print('nodes',nodes,'combo_leaves',len(leaves),'open_leaves',0)
print('least_negative_exact_margin',max(exact_margins))
