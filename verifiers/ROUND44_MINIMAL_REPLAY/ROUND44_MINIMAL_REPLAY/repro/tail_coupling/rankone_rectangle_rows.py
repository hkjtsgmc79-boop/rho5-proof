"""Exact quadratic four-entry coupling for the complete R43/R44 X chart.

No extra variables or quadratic monomials are required.  This module does not
change the original physical model: it supplies necessary rows for its LP outer
approximation.  See RANKONE_RECTANGLE_COUPLING.md for the proof and scope.
"""
from itertools import combinations, product
import sympy as s


def _rectangles(left, right, width, prefix, vs):
    result = []
    for (i, a), (j, b) in combinations(enumerate(left), 2):
        for (m, z), (n, t) in combinations(enumerate(right), 2):
            entries = (a*z, a*t, b*z, b*t)
            for signs in product((-1, 1), repeat=4):
                if signs[0]*signs[1]*signs[2]*signs[3] != -1:
                    continue
                label = ''.join('p' if q == 1 else 'm' for q in signs)
                name = f'{prefix}_{i}{j}_{m}{n}_{label}'
                expr = 2*width-sum(q*z for q, z in zip(signs, entries))
                result.append((name, s.Poly(expr, *vs)))
    return result


def rankone_rectangle_rows(vs, head_case=None, scope='all', normalize=True):
    """Return (name, Poly) rows, all in the convention polynomial >= 0.

    `scope='tail'` gives 24 rows on the actual last two rows/columns only.
    `scope='all'` gives 368 rows, including the real head arms and prefix.
    `scope='prefix'` gives 288 rows on the first rank-one packet only.
    `scope='stage'` gives 72 rows on the second rank-one packet only.
    `scope='core'` gives 8 rows on the core tail rank-one packet only.

    normalize=True uses precisely the R43 canonical signs e,beta>0,
    x0>0,q0<0,A<=0 and, when supplied, the I/II/III signs of u0,v0.
    No magnitude bound from the old k>=2.2 domain is used.
    """
    if scope not in ('all', 'tail', 'prefix', 'stage', 'core'):
        raise ValueError('Unknown rectangle scope')
    if head_case not in (None, 'I', 'II', 'III'):
        raise ValueError('Unknown head case')
    d = {str(z): z for z in vs}
    k, p, e, be = (d[z] for z in ('k', 'p', 'e', 'be'))
    A, B, c, cc = (d[z] for z in ('A', 'B', 'c', 'd'))
    u = [d[f'u{i}'] for i in range(3)]
    x = [d[f'x{i}'] for i in range(3)]
    v = [d[f'v{i}'] for i in range(3)]
    q = [d[f'q{i}'] for i in range(3)]
    left_o, right_o = [be]+u, [e]+v
    left_s, right_s = list(x), list(q)
    left_d, right_d = [c, cc], [A, B]
    if normalize:
        left_o[0], right_o[0] = 2*be-1, 2*e-1
        if head_case:
            su = 1 if head_case in ('I', 'II') else -1
            sv = 1 if head_case in ('I', 'III') else -1
            left_o[1], right_o[1] = 2*u[0]-su, 2*v[0]-sv
        left_s[0], right_s[0] = 2*x[0]-1, 2*q[0]+p
        right_d[0] = 2*A+k
    if scope == 'tail':
        left_o, right_o = u[1:], v[1:]
        left_s, right_s = x[1:], q[1:]
    rows = []
    tag = 'normalized' if normalize else 'plain'
    if scope in ('all', 'tail', 'prefix'):
        rows += _rectangles(left_o, right_o, s.Integer(1), 'rectangle_O_'+tag, vs)
    if scope in ('all', 'tail', 'stage'):
        rows += _rectangles(left_s, right_s, p, 'rectangle_S_'+tag, vs)
    if scope in ('all', 'tail', 'core'):
        rows += _rectangles(left_d, right_d, k, 'rectangle_D_'+tag, vs)
    assert all(poly.total_degree() <= 2 for _, poly in rows)
    return rows


def append_rankone_rectangles(model_tuple, head_case=None, scope='all', normalize=True):
    """Adapter for build_large_model.model(...), preserving its return schema."""
    vs, D, rows, lo, hi, target = model_tuple
    extra = rankone_rectangle_rows(vs, head_case, scope, normalize)
    return vs, D, list(rows)+extra, lo, hi, target
