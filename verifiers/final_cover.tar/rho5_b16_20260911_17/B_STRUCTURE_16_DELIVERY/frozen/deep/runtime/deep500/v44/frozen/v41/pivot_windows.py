"""Optional source-valid three-pivot inequalities and cycle facets.
See theory/PIVOT_WINDOWS.md. These are NOT X-specific high-r assumptions.
"""
from itertools import combinations, product
from source_access import fs
Q, I = fs.Q, fs.I
var, add, mul, scale, poly = fs.var, fs.add, fs.mul, fs.scale, fs.poly
k,p,r,F = [var(n) for n in ('k','p','r','F')]
PARAMETERS = tuple(Q(j,8) for j in range(8,17))
WINDOW_ROWS = [
 ('W123', add(scale(p,3),scale(mul(p,p),-1),scale(k,-1))),
 ('W234', add(scale(mul(p,k),3),scale(mul(k,k),-1),scale(mul(p,r),-1))),
 ('W345', add(scale(mul(k,r),3),scale(mul(r,r),-1),scale(mul(k,F),-1))),
]
for h in PARAMETERS:
    WINDOW_ROWS.extend([
      ('T123_'+str(h),add(poly(h*h),scale(p,3-2*h),scale(k,-1))),
      ('T234_'+str(h),add(scale(p,h*h),scale(k,3-2*h),scale(r,-1))),
      ('T345_'+str(h),add(scale(k,h*h),scale(r,3-2*h),scale(F,-1))),
    ])
PACKS = (((10,11,12,13),(9,17,18,19)),
         ((14,15,16),(20,21,22)),
         ((6,7),(0,4,5)))
def cycle_rows(aux):
    """Exact, box-dependent CHSH facets of actual two-by-two factor packets.
    Skip zero widths, never divide by a possibly zero width.
    """
    boxes=[I(*z) for z in aux];out=[]
    for family,(left,right) in enumerate(PACKS):
      for ii in combinations(left,2):
       for jj in combinations(right,2):
        widths=[boxes[z].hi-boxes[z].lo for z in ii+jj]
        if any(d==0 for d in widths):continue
        centers={z:add(scale(var(fs.NAMES[z]),2),poly(-boxes[z].lo-boxes[z].hi)) for z in ii+jj}
        den=widths[0]*widths[1]*widths[2]*widths[3]
        for eps in product((-1,1),repeat=4):
         if eps[0]*eps[1]*eps[2]*eps[3]!=-1:continue
         value=poly(2*den)
         for i in range(2):
          for j in range(2):
           value=add(value,scale(mul(centers[ii[i]],centers[jj[j]]),-eps[2*i+j]*widths[1-i]*widths[3-j]))
         out.append((f'cycle_{family}_{ii}_{jj}_{eps}',value))
    return out
