"""R44 quadratic tail cuts using a same-source positive head product G.

I: G=e*be; II: G=e*u0; III: G=be*v0.
The caller must bind G to that actual product, and certify g<=G<=1.
No T variable is introduced: every T below is the original u_i*v_j
monomial, shared globally with the physical O rows.
"""
import sympy as s


def anchor_tail_expressions(vs, head_case, anchor="G"):
    if head_case not in ("I", "II", "III"):
        raise ValueError("head_case must be I, II or III")
    sym = {str(v): v for v in vs}
    G = sym[str(anchor)]
    e, be = sym["e"], sym["be"]
    u = [sym[f"u{i}"] for i in range(3)]
    v = [sym[f"v{i}"] for i in range(3)]
    if head_case == "I":
        source, E, H = e*be, [e*u[i] for i in (1,2)], [be*v[j] for j in (1,2)]
    elif head_case == "II":
        source, E, H = e*u[0], [e*u[i] for i in (1,2)], [u[0]*v[j] for j in (1,2)]
    else:
        source, E, H = be*v[0], [v[0]*u[i] for i in (1,2)], [be*v[j] for j in (1,2)]
    T = {(i,j): u[i]*v[j] for i in (1,2) for j in (1,2)}
    return G, source, E, H, T


def anchor_tail_projected_rows(vs, head_case, g, *, anchor="G", include_plain=False):
    """Return 16 new (name, Poly) rows, using current certified lo[G] as g.

    If include_plain=True, also return 16 ordinary four-entry rows.
    All rows use only the original monomials plus the existing G variable.
    The caller supplies a legally established lower bound g; checking that
    g is rational and in [0,1] cannot by itself certify an arbitrary root.
    """
    vs = tuple(vs)
    g = s.Rational(g)
    if not 0 <= g <= 1:
        raise ValueError("the certified anchor lower bound must lie in [0,1]")
    G, _, E, H, T = anchor_tail_expressions(vs, head_case, anchor)
    rows = []
    for i in (1,2):
        for j in (1,2):
            Eij, Hij, Tij = E[i-1], H[j-1], T[i,j]
            for sign, tag in ((1,"p"),(-1,"m")):
                rows.append((f"anchor_new_sum_{i}{j}_{tag}",
                             s.Poly(1-g+G+g*Tij+sign*(Eij+Hij), *vs)))
                rows.append((f"anchor_new_diff_{i}{j}_{tag}",
                             s.Poly(1-g+G-g*Tij+sign*(Eij-Hij), *vs)))
                if include_plain:
                    rows.append((f"anchor_plain_sum_{i}{j}_{tag}",
                                 s.Poly(2-G+Tij+sign*(Eij+Hij), *vs)))
                    rows.append((f"anchor_plain_diff_{i}{j}_{tag}",
                                 s.Poly(2-G-Tij+sign*(Eij-Hij), *vs)))
    assert all(p.total_degree() <= 2 for _,p in rows)
    return rows


def head_anchor_tail_lift(vs, rows, lower, upper, *, head_case,
                          anchor="G", bind_anchor=False, root_grid=10**9):
    """Optional 4-variable/4-product lift; 24 incremental rows.

    G must already be a real variable with its true defining equality.
    bind_anchor=True duplicates that equality explicitly (26 rows instead).
    The default new roots are conservative actual product bounds intersected
    with [-1,1], rounded outward. Scalar products E_i*H_j share a single
    dictionary, while T=u_i*v_j stays the original quadratic monomial.
    """
    vs = tuple(vs)
    G, source, E, H, T = anchor_tail_expressions(vs, head_case, anchor)
    idx = vs.index(G)
    g = s.Rational(lower[idx])
    if not (0 <= g <= s.Rational(upper[idx]) <= 1):
        raise ValueError("G root must certify 0 <= g <= G <= 1")
    bounds = {v:(s.Rational(l),s.Rational(h)) for v,l,h in zip(vs,lower,upper)}
    names = [f"AE{i}" for i in (1,2)]+[f"AH{j}" for j in (1,2)]
    if any(str(v) in names for v in vs):
        raise ValueError("anchor-tail auxiliary variable name already used")
    extra_vs = tuple(s.Symbol(z) for z in names)
    new_vs = vs+extra_vs
    new_lo, new_hi = list(map(s.Rational,lower)), list(map(s.Rational,upper))
    additions = []

    def equal(name, expr):
        additions.extend([(name+"+",expr),(name+"-",-expr)])

    definitions = dict(zip(extra_vs,E+H))
    for z, expr in definitions.items():
        factors = list(expr.args)
        if len(factors)!=2 or any(a not in bounds for a in factors):
            raise ValueError("expected product of two original real factors")
        vals = [a*b for a in bounds[factors[0]] for b in bounds[factors[1]]]
        lz, hz = max(-s.Integer(1),min(vals)), min(s.Integer(1),max(vals))
        if root_grid:
            lz=s.Rational(s.floor(lz*root_grid),root_grid)
            hz=s.Rational(s.ceiling(hz*root_grid),root_grid)
        if lz>hz:
            raise ValueError("empty actual head-arm product interval")
        new_lo.append(lz);new_hi.append(hz)
        equal("anchor_def_"+str(z),z-expr)
    if bind_anchor:
        equal("anchor_true_G",G-source)
    for i in (1,2):
        for j in (1,2):
            Z=extra_vs[i-1]*extra_vs[2+j-1]
            Tij=T[i,j]
            formulas=(Z+G-g*Tij-g, 1-G-Tij+Z,
                      1-G+Tij-Z, G-g+g*Tij-Z)
            for n, expr in enumerate(formulas):
                additions.append((f"anchor_link_{i}{j}_{n}",expr))
    original_exprs=[(n,p.as_expr() if isinstance(p,s.Poly) else p) for n,p in rows]
    new_rows=[(n,s.Poly(expr,*new_vs)) for n,expr in original_exprs+additions]
    assert all(p.total_degree()<=2 for _,p in new_rows)
    manifest=dict(schema="rho5.cqg.head-anchor-tail-link.v1",head_case=head_case,
                  anchor=str(G),anchor_definition=str(source),anchor_lower=str(g),
                  added_variables=4,added_products=4,added_rows=len(additions),
                  real_definitions={str(z):str(expr) for z,expr in definitions.items()},
                  tail_variable_added=False,original_rows_preserved=True,
                  root_bound_obligation="Caller-certified original roots, including lo[G].",
                  height_credit="none")
    return new_vs,new_rows,new_lo,new_hi,manifest
