"""Version high_value_v1: exact necessary-inequality contraction.
All contractions are necessary for the same physical canonical image with F>=gamma.
"""
from fractions import Fraction as Q
from interval_capacity import I,GAMMA,ALPHA,CENTERS

class Empty(Exception):pass

def contract(aux,rounds=8):
    b=[v if isinstance(v,I)else I(*v)for v in aux]
    if len(b)!=24:raise ValueError('24 B auxiliary coordinates required')
    def cut(i,lo=None,hi=None):
        old=b[i];lo=old.lo if lo is None else max(old.lo,Q(lo));hi=old.hi if hi is None else min(old.hi,Q(hi))
        if lo>hi:raise Empty('high_value_coordinate_'+str(i))
        b[i]=I(lo,hi)
    try:
        for iteration in range(rounds):
            previous=[v.data()for v in b]
            r,s,t,p,e,beta,F=[b[i]for i in (1,2,3,8,9,10,23)]
            cut(8,hi=1+e.hi*beta.hi)
            positive=b[8].lo-1
            if positive>0:
                if beta.hi<=0 or e.hi<=0:raise Empty('high_value_positive_head')
                cut(9,lo=positive/beta.hi);cut(10,lo=positive/e.hi)
            cut(2,lo=F.lo-r.hi,hi=r.hi);cut(3,lo=F.lo-r.hi,hi=r.hi)
            cut(1,lo=max(b[2].lo,b[3].lo,F.lo-b[2].hi,F.lo-b[3].hi,F.lo/2),hi=F.hi)
            r,s,t,F=[b[i]for i in (1,2,3,23)]
            product_lo=max(Q(0),min(r.lo*(F.lo-r.lo),r.hi*(F.lo-r.hi)))
            vertex=F.hi/2
            product_hi=F.hi**2/4 if r.lo<=vertex<=r.hi else max(r.lo*(F.hi-r.lo),r.hi*(F.hi-r.hi))
            if product_hi<0:raise Empty('high_value_product_upper')
            if product_lo>0:
                if t.hi<=0 or s.hi<=0:raise Empty('high_value_positive_product')
                cut(2,lo=product_lo/t.hi);cut(3,lo=product_lo/s.hi)
            if b[3].lo>0:cut(2,hi=product_hi/b[3].lo)
            if b[2].lo>0:cut(3,hi=product_hi/b[2].lo)
            r,s,t,p=[b[i]for i in (1,2,3,8)]
            cut(23,hi=min(r.hi+s.hi,r.hi+t.hi,r.hi+s.hi*t.hi/r.hi,4*p.hi))
            if [v.data()for v in b]==previous:break
        return {'status':'BOUNDED','aux_image':[v.data()for v in b],'rounds':iteration+1}
    except Empty as error:
        return {'status':'EMPTY','reason':str(error)}

def oracle_from_base(base, *, local_ports=True):
    if base['status']=='EMPTY':return base
    contracted=contract(base['aux_image'])
    if contracted['status']=='EMPTY':return contracted
    b=[I(*v)for v in contracted['aux_image']]
    gap=[b[0],b[1],-b[1],*b[4:11],*b[11:23]]
    # b[4:11] is A,B,c,d,p,e,beta; the same 24-dimensional negative-D gap dictionary.
    for axis,old in ((2,base['gap_image'][22]),(3,base['gap_image'][23])):
        interval=(b[1]-b[axis]).intersection(I(0,b[1].hi))
        interval=interval.intersection(I(*old))if interval is not None else None
        if interval is None:return {'status':'EMPTY','reason':'high_value_gap_image'}
        gap.append(interval)
    out={**base,'status':'OPEN','aux_image':contracted['aux_image'],'gap_image':[v.data()for v in gap],
         'height_upper':str(b[23].hi),'contraction_rounds':contracted['rounds']}
    for key in ('port','budget','gain_lower'):out.pop(key,None)
    if b[23].hi<=ALPHA:return {**out,'status':'SAFE','port':'height'}
    for j,center in enumerate(CENTERS if local_ports else []):
        distance=max(max(abs(v.lo-c),abs(v.hi-c))for v,c in zip(gap,center))
        budget=distance+3*(gap[22].hi+gap[23].hi)
        if budget<Q(1,1250):return {**out,'status':'SAFE','port':f'canonical_flow_{j}','budget':str(budget),'gain_lower':str((gap[22].lo+gap[23].lo)/10)}
    return out
