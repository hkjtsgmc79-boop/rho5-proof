"""Same-source correction lifts for the R44 complete real X model.

All additions are identities of x*q.T and u*v.T.  Retain every original
physical/head/budget row.  This module does not certify a height theorem.
See SAME_SOURCE_PACKET_LIFT.md for scope, proofs and exact scale counts.
"""
from itertools import combinations
import sympy as s


SHAPES = {
    "tail": [(i, j) for i in (1, 2) for j in (1, 2)],
    "bottom": [(i, j) for i in (1, 2) for j in (0, 1, 2)],
    "full": [(i, j) for i in (0, 1, 2) for j in (0, 1, 2)],
}


def packet_lift(vs, rows, lower, upper, *, shape="tail", minors="all",
                incidence="all", root_grid=10**9):
    """Append real packet variables and redundant quadratic identities.

    Input rows are (name, Poly or expression), interpreted as expression>=0.
    The original rows remain byte-for-expression unchanged. Their monomials
    must use a single shared product dictionary with the new defining rows.

    shapes: tail=2x2; bottom=2x3; full=3x3 per packet.
    minors: none, anchor (00 minors, full only), all.
    incidence: none, anchor (factor index 0, full only), all.

    Returns (new_vs, new_rows, new_lower, new_upper, manifest).
    An equality is exported as two opposite nonnegative rows so existing
    exact McCormick kernels can consume it without a special row type.
    """
    if shape not in SHAPES:
        raise ValueError("unknown shape")
    if minors not in ("none", "anchor", "all"):
        raise ValueError("unknown minor selection")
    if incidence not in ("none", "anchor", "all"):
        raise ValueError("unknown incidence selection")
    if shape != "full" and (minors == "anchor" or incidence == "anchor"):
        raise ValueError("00-anchor selections require full shape")
    vs = tuple(vs)
    pos = {str(v): n for n, v in enumerate(vs)}
    sym = {str(v): v for v in vs}
    if any(f"{P}{i}{j}" in pos for P in ("X", "Y") for i, j in SHAPES[shape]):
        raise ValueError("packet lift variable already present")
    original_bounds = {v: (s.Rational(lower[n]), s.Rational(upper[n]))
                       for n, v in enumerate(vs)}

    def product_bounds(a, b):
        aa, bb = original_bounds[a], original_bounds[b]
        candidates = [x*y for x in aa for y in bb]
        return min(candidates), max(candidates)

    cells = SHAPES[shape]
    packets = {}
    definitions = {}
    new_lo, new_hi = list(map(s.Rational, lower)), list(map(s.Rational, upper))
    new_vs = list(vs)
    for name, left, right in (("X", "x", "q"), ("Y", "u", "v")):
        factors = ([sym[f"{left}{i}"] for i in range(3)],
                   [sym[f"{right}{j}"] for j in range(3)])
        Z = {(i, j): s.Symbol(f"{name}{i}{j}") for i, j in cells}
        packets[name] = (Z, factors)
        for i, j in cells:
            a, b = factors[0][i], factors[1][j]
            z = Z[i, j]
            lz, hz = product_bounds(a, b)
            if name == "X" and (i, j) == (0, 0):
                # |q0|<=p, |x0|<=1; S00=k+X00<=p.
                pmax = original_bounds[sym["p"]][1]
                kmin = original_bounds[sym["k"]][0]
                lz, hz = max(lz, -pmax), min(hz, pmax-kmin)
                # O00=k+X00+u0*v0<=1, retaining actual Y00 bounds.
                ylo, _ = product_bounds(sym["u0"], sym["v0"])
                hz = min(hz, 1-kmin-ylo)
            if lz > hz:
                raise ValueError(f"empty necessary root interval for {z}")
            if root_grid:
                lz = s.Rational(s.floor(lz*root_grid), root_grid)
                hz = s.Rational(s.ceiling(hz*root_grid), root_grid)
            new_vs.append(z)
            new_lo.append(lz)
            new_hi.append(hz)
            definitions[z] = a*b

    additions = []
    counts = {"definition": 0, "minor": 0, "incidence": 0}

    def equality(kind, name, expression):
        counts[kind] += 1
        expression = s.expand(expression)
        additions.extend([(name+"+", expression), (name+"-", -expression)])

    for name, (Z, (a, b)) in packets.items():
        for i, j in cells:
            equality("definition", f"lift_{name}{i}{j}", Z[i, j]-a[i]*b[j])
        for i, h in combinations(range(3), 2):
            for j, l in combinations(range(3), 2):
                if all(t in Z for t in ((i,j),(i,l),(h,j),(h,l))):
                    if minors == "none" or (minors == "anchor" and (i,j)!=(0,0)):
                        continue
                    equality("minor", f"minor_{name}_{i}{h}_{j}{l}",
                             Z[i,j]*Z[h,l]-Z[i,l]*Z[h,j])
        if incidence != "none":
            for i, h in combinations(range(3), 2):
                if incidence == "anchor" and i != 0:
                    continue
                for j in range(3):
                    if (i,j) in Z and (h,j) in Z:
                        equality("incidence", f"left_{name}_{i}{h}_{j}",
                                 a[i]*Z[h,j]-a[h]*Z[i,j])
            for j, l in combinations(range(3), 2):
                if incidence == "anchor" and j != 0:
                    continue
                for i in range(3):
                    if (i,j) in Z and (i,l) in Z:
                        equality("incidence", f"right_{name}_{i}_{j}{l}",
                                 b[j]*Z[i,l]-b[l]*Z[i,j])

    new_vs = tuple(new_vs)
    all_exprs = [(n, p.as_expr() if isinstance(p, s.Poly) else p) for n, p in rows]
    all_exprs.extend(additions)
    new_rows = [(n, s.Poly(e, *new_vs)) for n, e in all_exprs]
    if any(p.total_degree() > 2 for _, p in new_rows):
        raise ValueError("input or generated row is not quadratic")
    monomials = {m for _, p in new_rows for m, _ in p.terms() if sum(m) == 2}
    original_monomials = {
        m for _, p in rows
        for m, _ in s.Poly(p.as_expr() if isinstance(p,s.Poly) else p,*vs).terms()
        if sum(m) == 2
    }
    manifest = {
        "schema": "rho5.cqg.same-source-packet-lift.v1",
        "shape": shape, "minors": minors, "incidence": incidence,
        "original_variables": len(vs), "added_variables": len(new_vs)-len(vs),
        "variables": len(new_vs), "products": len(monomials),
        "added_products": len(monomials)-len(original_monomials),
        "original_rows": len(rows), "added_rows": len(additions),
        "rows": len(new_rows), "equalities": counts,
        "definitions": {str(z): str(e) for z,e in definitions.items()},
        "necessity": "Every physical original point has its unique actual packet extension.",
        "height_credit": "none; a new exact bound requires a model-bound complete certificate",
    }
    return new_vs, new_rows, new_lo, new_hi, manifest
