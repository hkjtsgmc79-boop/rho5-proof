"""Conservative whole-box checker for the NEW two-gap theorem, not a B tree engine.

Interpretation is conditional on one complete physical source represented by the
box. Independent variable/packet feasibility is NOT asserted. The theorem's
rational certificate must have been verified before this rule is consumed.
"""
from fractions import Fraction as Q
from gap_model import NAMES

def rational(x):
    if isinstance(x, (float, bool)):
        raise TypeError('Use exact rationals, integers or rational strings')
    return Q(x)

def intervals(box, n):
    if len(box) != n:
        raise ValueError('wrong coordinate count')
    out = [(rational(a), rational(b)) for a,b in box]
    if any(a>b for a,b in out):
        raise ValueError('reversed interval')
    return out

def flow_cases(box, certificate):
    box=intervals(box,24)
    if certificate['schema'] != 'V36_TWO_GAP_FLOW_V1':
        raise ValueError('wrong theorem identity')
    if certificate['coordinate_order'] != list(NAMES):
        raise ValueError('wrong coordinate identity')
    radius=rational(certificate['outer_radius'])
    speed=rational(certificate['speed_cap'])
    if radius != Q(1,1250) or speed != 3:
        raise ValueError('changed theorem constants')
    # These are conservative guards; actual source positivity is also required.
    if box[1][0]<=0 or min(box[22][0],box[23][0])<0:
        return []
    budget=speed*(box[22][1]+box[23][1])
    good=[]
    for case in certificate['cases']:
        center=list(map(Q,case['center']))
        dist=max(max(abs(a-c),abs(b-c)) for (a,b),c in zip(box,center))
        if dist+budget<radius:
            good.append(case['case'])
    return good

def negative_d_box_to_gap_box(box):
    """Rigorous affine enclosure of w=-r, sigma=r-s, tau=r-t.
    Input order is build_b_models.NAMES and includes the TRUE height coordinate F.
    Interval overestimation is permitted; no corner sampling or root relabeling.
    """
    from build_b_models import NAMES as BN
    box=intervals(box,len(BN));d=dict(zip(BN,box))
    rlo,rhi=d['r'];slo,shi=d['s'];tlo,thi=d['t']
    d['w']=(-rhi,-rlo);d['sigma']=(rlo-shi,rhi-slo);d['tau']=(rlo-thi,rhi-tlo)
    return [d[n] for n in NAMES]
