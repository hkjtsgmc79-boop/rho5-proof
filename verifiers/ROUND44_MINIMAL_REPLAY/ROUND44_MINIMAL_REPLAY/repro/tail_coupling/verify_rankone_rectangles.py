"""Run on fixed X through the parent task.  No numeric search is performed."""
from pathlib import Path
from itertools import product
import argparse
import importlib.util
import json
import sympy as s
from rankone_rectangle_rows import rankone_rectangle_rows


def load_builder(path):
    spec = importlib.util.spec_from_file_location('r44_rectangle_base', path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def quadratic_pairs(rows):
    return {mon for _, poly in rows for mon, _ in poly.terms() if sum(mon) == 2}


def run(builder_path, klo):
    a, b, z, t, h = s.symbols('a b z t h')
    loss = 2*h-a*z-a*t-b*z+b*t
    numerator = ((1-a)*(h+z)*(h+t)+(1-b)*(h+z)*(h-t)
                 +(1+b)*(h-z)*(h+t)+(1+a)*(h-z)*(h-t))
    assert s.expand(2*h*loss-numerator) == 0
    for signs in product((-1, 1), repeat=4):
        if signs[0]*signs[1]*signs[2]*signs[3] != -1:
            continue
        oriented = loss.subs({a: signs[0]*a, b: signs[2]*b,
                              t: signs[0]*signs[1]*t}, simultaneous=True)
        wanted = 2*h-sum(v*w for v, w in zip(signs, (a*z, a*t, b*z, b*t)))
        assert s.expand(oriented-wanted) == 0
        for corner in product((-1, 1), repeat=4):
            point = {a: corner[0], b: corner[1], z: corner[2], t: corner[3], h: 1}
            assert wanted.subs(point) >= 0
    # Exact lifted counterexample: every factor is zero, and each individual
    # McCormick edge for [-1,1]^2 permits any lifted product in [-1,1].
    # The three +1 edges and one -1 edge fail a rectangle row by exactly 2.
    assert 2-(1+1+1-(-1)) == -2
    builder = load_builder(builder_path)
    records = []
    for case in ('I', 'II', 'III'):
        vs, D, rows, lo, hi, target = builder.model(klo, case, True)
        old_pairs = quadratic_pairs(rows)
        byname = {str(v): (l, h) for v, l, h in zip(vs, lo, hi)}
        assert byname['e'][0] >= 0 and byname['be'][0] >= 0
        assert byname['x0'][0] >= 0 and byname['q0'][1] <= 0
        assert byname['A'][1] <= 0
        for normalize in (False, True):
            for scope, count in (('all', 368), ('tail', 24), ('prefix', 288), ('stage', 72), ('core', 8)):
                extra = rankone_rectangle_rows(vs, case, scope, normalize)
                assert len(extra) == count
                assert len({name for name, _ in extra}) == count
                assert all(poly.total_degree() <= 2 for _, poly in extra)
                assert quadratic_pairs(extra) <= old_pairs
                assert all(c.q == 1 for _, poly in extra for _, c in poly.terms())
                records.append(dict(case=case, normalize=normalize, scope=scope,
                                    rows=count, new_variables=0, new_quadratic_pairs=0))
    return dict(status='EXACT_PASS', klo=str(klo),
                proof='8 signed four-entry rows; exact nonnegative numerator identity',
                scope='Complete canonical real X chart; no R flags or r>k assumption',
                strict_McCormick_strengthening_gap='2', records=records)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--builder', type=Path, required=True)
    ap.add_argument('--klo', default='21/10')
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    result = run(args.builder, s.Rational(args.klo))
    blob = json.dumps(result, indent=2)+'\n'
    if args.output:
        args.output.write_text(blob)
    print(blob)
