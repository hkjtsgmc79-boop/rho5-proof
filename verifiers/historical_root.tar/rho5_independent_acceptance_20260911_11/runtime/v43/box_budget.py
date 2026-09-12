"""Read-only V43 interval port for the physical subset of a supplied X22 box.

This module is NOT a complete B-parent proof wrapper. The caller must establish
that this is the enclosure of the SAME actual complete X transport target,
and must certify D-transport qualification / sorting branches where relevant.
"""
from fractions import Fraction as Q
from itertools import product
import json
import local_guard as g

def validate_box(box):
    g.need(isinstance(box,list) and len(box)==22,'X22 box')
    ans=[]
    for row in box:
        g.need(isinstance(row,(list,tuple)) and len(row)==2,'interval pair')
        lo,hi=map(g.exact_q,row);g.need(lo<=hi,'ordered endpoints');ans.append((lo,hi))
    return ans

def mul_iv(a,b):
    pp=[x*y for x in a for y in b];return min(pp),max(pp)
def interval(poly,box):
    lo=hi=Q(0)
    for mon,co in poly.items():
        v=(co,co)
        for i in mon:v=mul_iv(v,box[i])
        lo+=v[0];hi+=v[1]
    return lo,hi

def x_budget(box,case):
    box=validate_box(box);g.need(type(case)is int and 0<=case<4,'case')
    b3,_,_=g.source();center,_,_=g.chart_data(case,False)
    distance=max(max(abs(lo-c),abs(hi-c))for (lo,hi),c in zip(box,center))
    if distance>g.RADIUS:return dict(status='OPEN_OUTSIDE_CERTIFIED_CUBE',distance_upper=distance)
    poly=b3.lm.add(b3.lm.source()['O12+'],b3.lm.source()['O22-'])
    slack_lower=max(Q(0),interval(poly,box)[0])
    margin=min(slack_lower/16,(g.RADIUS-distance)/36)
    return dict(status='CONDITIONAL_PHYSICAL_X_HEIGHT_BUDGET',case=case,distance_upper=distance,
        joint_corner_slack_lower=slack_lower,alpha_minus_FX_lower=margin,
        P0_automatically_positive_on_box=interval(b3.lm.source()['P0-'],box)[0]>0)

def b_transport_budget(box,loss_upper,case,route):
    """Conditional B03-route corollary. Does NOT certify the transport itself."""
    g.need(route in ('R','D'),'known transport R or D')
    box=validate_box(box);ell=g.exact_q(loss_upper);g.need(ell>=0,'nonnegative loss upper')
    g.need(type(case)is int and 0<=case<4,'case')
    center,_,_=g.chart_data(case,False)
    d=max(max(abs(lo-c),abs(hi-c))for (lo,hi),c in zip(box,center))
    return dict(status='CONDITIONAL_ALPHA_SAFE'if d+g.B_COSTS[case]*ell<=g.RADIUS else'OPEN',
      route=route,case=case,distance_upper=d,loss_upper=ell,cost=g.B_COSTS[case],score=d+g.B_COSTS[case]*ell,
      assumptions='Same complete physical B source and X target; all sorting branches covered; D guard when used; true loss <= loss_upper. This record alone is not a parent proof.')

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('input');a=ap.parse_args();v=json.loads(open(a.input).read())
    if 'route'in v:out=b_transport_budget(v['box'],v['loss_upper'],v['case'],v['route'])
    else:out=x_budget(v['box'],v['case'])
    print(json.dumps(g.jsonable(out),indent=2))
