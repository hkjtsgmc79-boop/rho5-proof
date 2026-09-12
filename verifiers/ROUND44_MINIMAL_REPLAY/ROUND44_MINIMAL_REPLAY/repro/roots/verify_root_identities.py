"""Exact audit for the Round44 roots/head-product augmentation; no search.

Run on X as part of the main task's new-model audit.  --output writes JSON.
The proof of inequalities is the adjacent note, not this finite audit.
"""
import argparse
import json
from pathlib import Path
import sympy as s
from augment_midband_roots import augment_model, sqrt_bounds, head_product_lower, type_i_x_lower


def main():
    checks = {}

    def check(name, value):
        if s.cancel(s.expand(value)) != 0:
            raise AssertionError(name)
        checks[name] = True

    e, be, u, v, z, p, k, S, x, h, b, g = s.symbols('e be u v z p k S x h b g')
    t, d, G, lam = s.symbols('t d G lam')
    a = t - d
    check('unified_product_tangent', G - (2 * lam - lam**2) * t - lam**2 * d
          - (G * a - t**2) / a - (t - lam * a)**2 / a)

    A = 1 - (b - 1) * (h - 1) / g + b * h / p
    E = p + 1 - (p - 1)**2 / g
    check('I_monotone_endpoint', E - A - (p - b) * (h / p - (h - 1) / g)
          - (p - h) * (1 - (p - 1) / g))
    O = S - u * z
    ii_rhs = (u - be) * (p - S) + be * (1 - O) + u * (1 - h - be * z) + u * (1 - x) * h
    check('II_quadratic_precursor', (u * (p + 1 - k) - be * (p - 1) - ii_rhs).subs(k, S + x * h))
    check('II_product_transfer', e * u * (p + 1 - k) - (p - 1)**2
          - e * (u * (p + 1 - k) - be * (p - 1)) - (p - 1) * (e * be - p + 1))

    C1, C2 = (1 - u) * v - d, u * (1 - v) - d
    check('I_u_square', (1 - u) * C2 + u * C1 - (u * (1 - u) - d))
    check('I_v_square', v * C2 + (1 - v) * C1 - (v * (1 - v) - d))
    C1, C2 = (be - u) * v - d, (e - v) * u - d
    check('I_generalized_u_square', (be - u) * C2 + u * C1 - (e * u * (be - u) - be * d))
    check('I_generalized_v_square', v * C2 + (e - v) * C1 - (be * v * (e - v) - e * d))
    ii_cubic = (1 - z) * (1 - O) + z * (p - S) + z * (be - p + 1) + (1 - h - be * z) + (1 - x) * h
    check('II_receiver_cubic', (2 + u * z * (1 - z) - k - ii_cubic).subs(k, S + x * h))
    check('II_refined_receiver_transfer', 2 + u * z * (1 - z / e)
          - (1 + z / e + (1 - z / e) * (1 + u * z)))

    # Tangency constants and sign of the second derivative are proved in the
    # note; verify each encoded rational tangent's value and derivative.
    for sv, intercept, slope in ((s.Rational(3, 4), s.Rational(6075, 1024), s.Rational(-15, 16)),
                                 (s.Rational(3, 5), s.Rational(972, 125), s.Rational(-9, 5)),
                                 (s.Rational(1, 2), s.Rational(1225, 128), s.Rational(-21, 8))):
        ks, ps = (9 - sv**2) / 4, (3 + sv) / 2
        check('tangent_value_' + str(sv), intercept + slope * ks - ks * ps)
        check('tangent_slope_' + str(sv), slope - ps + ks / sv)

    root_checks, row_counts = [], {}
    vs = s.symbols('k r w A B c d p e be u0 u1 u2 x0 x1 x2 v0 v1 v2 q0 q1 q2')
    for K in (s.Rational(21, 10), s.Rational(43, 20), s.Rational(11, 5)):
        for case in ('I', 'II', 'III'):
            lo = [K, s.Rational(4132517, 2000000), -s.Rational(9, 4), -s.Rational(9, 4),
                  -s.Rational(9, 4), -1, -1, s.Rational(4132517, 4000000), 0, 0] + [-1] * 9 + [-2] * 3
            hi = [s.Rational(9, 4), 4, s.Rational(-132517, 1000000), 0, s.Rational(9, 4),
                  1, 1, 2, 1, 1] + [1] * 9 + [2] * 3
            rows, low, high = augment_model(vs, [], lo, hi, K, s.Rational(11, 5), case)
            assert all(poly.total_degree() <= 2 for _, poly in rows)
            assert all(a <= b for a, b in zip(low, high))
            row_counts[case] = len(rows)
            root_checks.append({'klo': str(K), 'case': case,
                                'rhi': str(high[1]), 'w_hi': str(high[2]),
                                'p': [str(low[7]), str(high[7])],
                                'e': [str(low[8]), str(high[8])],
                                'beta': [str(low[9]), str(high[9])],
                                'u0': [str(low[10]), str(high[10])],
                                'v0': [str(low[16]), str(high[16])],
                                'x0': [str(low[13]), str(high[13])]})
        for value in (9 - 4 * K, K * (K - 2)):
            lower, upper = sqrt_bounds(value)
            assert lower * lower <= value <= upper * upper
    assert head_product_lower(s.Rational(21, 10), s.Rational(11, 10), s.Rational(19, 10)) == s.Rational(2, 5)
    assert head_product_lower(s.Rational(21, 10), s.Rational(3, 2), s.Rational(19, 10)) == s.Rational(5, 8)
    assert type_i_x_lower(s.Rational(21, 10), s.Rational(9, 5), s.Rational(19, 10)) == s.Rational(5, 6)
    result = {'status': 'R44_ROOT_HEAD_PRODUCT_EXACT_AUDIT_PASS',
              'identities': len(checks), 'checks': checks, 'added_rows': row_counts,
              'root_cases': root_checks,
              'scope': 'Exact identities, degree checks, rational outward-root checks; no continuous-domain tree conclusion.'}
    ap = argparse.ArgumentParser()
    ap.add_argument('--output')
    args = ap.parse_args()
    if args.output:
        Path(args.output).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
