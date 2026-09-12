"""R44 complete-X root and head-product cuts; see the adjacent proof note.

API: rows, lo, hi = augment_model(vs, rows, lo, hi, klo, khi, head_case)
Rows retain the Round43 (name, sympy.Poly) format.  Arguments are copied.
All root endpoints are rounded outwards.  No LP or other search is run.
"""
from math import isqrt
import sympy as s

GAMMA = s.Rational(4132517, 10**6)
DEFAULT_LAMBDAS = tuple(map(s.Rational, ('1', '9/8', '5/4', '3/2', '2', '3', '4', '6', '9')))


def sqrt_bounds(value, grid=10**12):
    """Exact rational lower/upper bounds on a nonnegative square root."""
    value = s.Rational(value)
    if value < 0:
        raise ValueError('Negative square-root argument')
    n = isqrt(int(value.p) * grid * grid // int(value.q))
    low = s.Rational(n, grid)
    high = low if low * low == value else s.Rational(n + 1, grid)
    return low, high


def head_product_lower(klo, plo, phi):
    """Min t^2/(t-(klo-2)) on a p slice; None if slice has t<=d only."""
    d, a, b = s.Rational(klo) - 2, s.Rational(plo) - 1, s.Rational(phi) - 1
    if b <= d:
        return None
    if b <= 2 * d:
        return b * b / (b - d)
    if a >= 2 * d:
        return a * a / (a - d)
    return 4 * d


def type_i_x_lower(klo, plo, phi):
    K, ell, P = map(s.Rational, (klo, plo, phi))
    rad = K * (K - 2)
    if (K - ell)**2 <= rad:  # Entire p interval is right of the minimizer.
        return (K - ell) / (ell * (2 - ell))
    if (K - P)**2 >= rad:  # Entire p interval is left of the minimizer.
        return (K - P) / (P * (2 - P))
    return (K - 1 + sqrt_bounds(rad)[0]) / 2


def augment_model(vs, rows, lo, hi, klo, khi, head_case, root_grid=10**9,
                  lambdas=DEFAULT_LAMBDAS):
    """Add proved quadratic cuts and outward root bounds to one head case.

    Preconditions: complete X physical model; e,beta>0,x0>0,q0<0,A<=0;
    case I/II/III has Round43's corresponding b,h and receiver signs.
    This API supports any 2<klo<=khi<=9/4, including p-sliced input roots.
    The fixed contradiction threshold is GAMMA, matching Round43/44.
    """
    K, J = map(s.Rational, (klo, khi))
    if not (2 < K <= J <= s.Rational(9, 4)):
        raise ValueError('Require 2 < klo <= khi <= 9/4')
    if head_case not in ('I', 'II', 'III'):
        raise ValueError('A proved head case I, II, or III is required')
    vs = tuple(vs)
    ix = {str(v): i for i, v in enumerate(vs)}
    vmap = dict(zip(map(str, vs), vs))
    k, r, w, p, e, be, u, v = (vmap[n] for n in ('k', 'r', 'w', 'p', 'e', 'be', 'u0', 'v0'))
    out = list(rows)
    lower, upper = list(map(s.Rational, lo)), list(map(s.Rational, hi))
    names = {name for name, _ in out}

    def add(name, expr):
        name = 'r44_roots_' + name
        if name in names:
            raise ValueError('Duplicate augmentation row: ' + name)
        names.add(name)
        poly = s.Poly(s.expand(expr), *vs)
        if poly.total_degree() > 2:
            raise AssertionError('Nonquadratic row: ' + name)
        out.append((name, poly))

    def tighten(name, low=None, high=None):
        i = ix[name]
        if low is not None:
            lower[i] = max(lower[i], s.Rational(low))
        if high is not None:
            upper[i] = min(upper[i], s.Rational(high))

    tighten('k', K, J)
    sqrt_hi = sqrt_bounds(9 - 4 * K)[1]
    pminus = (3 - sqrt_hi) / 2
    pplus = (3 + sqrt_hi) / 2
    tighten('p', max(GAMMA / 4, K / 2, pminus), min(4 / K, pplus))
    ell, P = lower[ix['p']], upper[ix['p']]
    if not (1 < ell <= P < 2):
        raise ValueError('Require a nonempty legitimate p interval inside (1,2)')

    # R(k)=k*p_+(k) is decreasing; the independent p-slice stage bound
    # maximizes the concave quadratic 3k-k^2/P on [K,J].
    stage_at = min(J, max(K, 3 * P / 2))
    Rhi = min(s.Rational(4), K * pplus, 3 * stage_at - stage_at**2 / P)
    tighten('r', GAMMA / 2, Rhi)
    Rhi = upper[ix['r']]
    tighten('w', -J, Rhi - GAMMA)
    tighten('A', -J, 0)
    tighten('B', -J, J)
    for n in ('e', 'be'):
        tighten(n, ell - 1, 1)
    tighten('x0', K / P - 1, 1)
    tighten('q0', -P, P - K)

    for a, b, name in ((s.Rational(6075, 1024), s.Rational(-15, 16), '135_64'),
                       (s.Rational(972, 125), s.Rational(-9, 5), '54_25'),
                       (s.Rational(1225, 128), s.Rational(-21, 8), '35_16')):
        add('r_tangent_' + name, a + b * k - r)

    G, factors = {'I': (e * be, (e, be)), 'II': (e * u, (e, u)),
                  'III': (be * v, (be, v))}[head_case]
    add('p_plus_one_minus_k', p + 1 - k)
    for n, lam in enumerate(lambdas):
        lam = s.Rational(lam)
        add('head_product_lambda_' + str(n), G - (2 * lam - lam**2) * (p - 1) - lam**2 * (k - 2))
    for factor in factors:
        add('factor_' + str(factor), factor * (p + 1 - k) - (p - 1)**2)

    # Each positive factor is at least G, since both factors are <=1.
    nu = head_product_lower(K, ell, P)
    if nu is not None:
        for factor in factors:
            tighten(str(factor), nu, 1)

    L, U = (1 - sqrt_hi) / 2, (1 + sqrt_hi) / 2
    if head_case == 'I':
        add('I_u_square', u - u**2 - k + 2)
        add('I_v_square', v - v**2 - k + 2)
        add('I_beta_u_square', be * u - u**2 - be * (k - 2))
        add('I_e_v_square', e * v - v**2 - e * (k - 2))
        tighten('u0', L, U)
        tighten('v0', L, U)
        tighten('x0', type_i_x_lower(K, ell, P), 1)
    elif head_case == 'II':
        add('II_v_square', -v - v**2 - k + 2)
        add('II_u_linear', u - 4 * k + 8)
        add('II_e_v_square', -e * v - v**2 - e * (k - 2))
        tighten('v0', -U, -L)
    else:
        add('III_u_square', -u - u**2 - k + 2)
        add('III_v_linear', v - 4 * k + 8)
        add('III_beta_u_square', -be * u - u**2 - be * (k - 2))
        tighten('u0', -U, -L)

    if root_grid:
        lower = [s.Rational(s.floor(z * root_grid), root_grid) for z in lower]
        upper = [s.Rational(s.ceiling(z * root_grid), root_grid) for z in upper]
    return out, lower, upper
