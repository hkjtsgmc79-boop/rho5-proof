"""Small, exact convex-square cuts for the existing R44 product dictionary.

Every returned row is the primitive integer expansion of a true square.
No variables or quadratic monomials may be added. Candidate selection first
rounds each original root endpoint OUTWARD to the 1/16 grid; this is invariant
under the existing outward 1e-9 root rounding because 10**9 is divisible by 16.
Frozen metadata includes every exact rational center for independent replay.
"""
from math import gcd
import sympy as s


MODES = {"minimal", "balanced", "core", "head"}


def _expressions(rows):
    return [(n,p.as_expr() if isinstance(p,s.Poly) else p) for n,p in rows]


def _quadratic_dictionary(vs, rows):
    result=set()
    for _,expr in _expressions(rows):
        for mon,_ in s.Poly(expr,*vs).terms():
            if sum(mon)==2:
                result.add(mon)
    return result


def _directions():
    result=[]
    for z in ("p","k","r"):
        result.append(("core_"+z,{z:1},"core"))
    for a,b in (("p","k"),("p","r"),("k","r")):
        for sign,tag in ((1,"plus"),(-1,"minus")):
            result.append((f"core_{a}_{tag}_{b}",{a:1,b:sign},"core"))
    for z in ("u0","v0"):
        result.append(("head_"+z,{z:1},"head"))
    result.extend([("head_u0_plus_v0",{"u0":1,"v0":1},"head"),
                   ("head_u0_minus_v0",{"u0":1,"v0":-1},"head")])
    return result


def _primitive_square(vs, coeffs, center):
    symbols={str(v):v for v in vs}
    center=s.Rational(center)
    linear=sum(s.Integer(a)*symbols[name] for name,a in coeffs.items())
    # center=m/n: (n*linear-m)^2 is a positive integer multiple of
    # (linear-center)^2. Primitive reduction never changes the sign.
    raw=s.Poly((center.q*linear-center.p)**2,*vs)
    divisor=0
    for _,c in raw.terms():
        if c.q!=1:
            raise AssertionError("noninteger square coefficient")
        divisor=gcd(divisor,abs(int(c)))
    if divisor==0:
        raise AssertionError("zero candidate direction")
    poly=s.Poly(raw.as_expr()/divisor,*vs)
    return poly,divisor


def moment_square_cuts(vs, rows, lo, hi, mode="balanced", *, max_rows=40):
    """Return (extra_rows, manifest), adding no variable or product.

    balanced: 1/16-grid endpoint midpoint and up to two +/-1/16 neighbors,
              on all dictionary-supported directions; at most 39 rows.
    minimal: one midpoint per supported direction; at most 13 rows.
    core: balanced selection on p,k,r and their pairwise sums/differences;
          at most 27 rows.
    head: balanced selection on u0,v0 and their sum/difference; at most 12.

    Neighbors are retained only inside the OUTWARD-QUANTIZED direction
    interval, never selected using the original unrounded endpoints.
    All centers have denominator dividing 32. They need not lie inside the
    original root box: a real square is nonnegative for every rational center.
    """
    if mode not in MODES:
        raise ValueError("unknown square-cut mode")
    if not isinstance(max_rows,int) or not 0<=max_rows<=40:
        raise ValueError("max_rows must be an integer from 0 through 40")
    vs=tuple(vs)
    if len(vs)!=len(lo) or len(vs)!=len(hi):
        raise ValueError("variable/root dimensions differ")
    roots={}
    for v,l,h in zip(vs,lo,hi):
        l,h=s.Rational(l),s.Rational(h)
        if l>h:
            raise ValueError("reversed input interval")
        roots[str(v)]=(s.Rational(s.floor(16*l),16),
                       s.Rational(s.ceiling(16*h),16))
    original_mons=_quadratic_dictionary(vs,rows)
    original_names={n for n,_ in rows}
    directions=[];skipped=[]
    symbols={str(v):v for v in vs}
    for label,coeffs,group in _directions():
        if mode in ("core","head") and group!=mode:
            continue
        if any(name not in symbols for name in coeffs):
            skipped.append({"direction":label,"reason":"missing original variable"})
            continue
        probe,_=_primitive_square(vs,coeffs,0)
        used={m for m,_ in probe.terms() if sum(m)==2}
        missing=used-original_mons
        if missing:
            missing_names=[]
            for mon in sorted(missing):
                missing_names.append("*".join(str(vs[i]) for i,p in enumerate(mon) for _ in range(p)))
            skipped.append({"direction":label,"reason":"missing quadratic monomial",
                            "missing":missing_names})
            continue
        lower=sum(a*roots[n][0 if a>0 else 1] for n,a in coeffs.items())
        upper=sum(a*roots[n][1 if a>0 else 0] for n,a in coeffs.items())
        center=(lower+upper)/2
        offsets=(s.Integer(0),) if mode=="minimal" else (s.Integer(0),-s.Rational(1,16),s.Rational(1,16))
        centers=[center+z for z in offsets if lower<=center+z<=upper]
        directions.append((label,coeffs,lower,upper,centers))
    # Centers of all supported directions get priority over neighbor rows.
    # For the default 39-row maximum no truncation is necessary.
    choices=[]
    for layer in range(3):
        for label,coeffs,lower,upper,centers in directions:
            if layer<len(centers):
                choices.append((label,coeffs,lower,upper,centers[layer],layer))
    extra=[];specs=[]
    for label,coeffs,lower,upper,center,layer in choices[:max_rows]:
        name=f"moment_square_{label}_{layer}"
        if name in original_names:
            raise ValueError("square-cut name already present: "+name)
        poly,divisor=_primitive_square(vs,coeffs,center)
        assert poly.total_degree()==2
        assert {m for m,_ in poly.terms() if sum(m)==2}<=original_mons
        extra.append((name,poly))
        specs.append(dict(name=name,direction=coeffs,center=str(center),
                          center_numerator=int(center.p),center_denominator=int(center.q),
                          primitive_divisor=divisor,
                          quantized_direction_interval=[str(lower),str(upper)]))
    used_names=sorted({name for _,coeffs,_,_,_ in directions for name in coeffs})
    manifest=dict(schema="rho5.cqg.moment-square-cuts.v1",mode=mode,
                  root_quantization="outward to 1/16 before any selection",
                  quantized_roots={n:list(map(str,roots[n])) for n in used_names},
                  exact_rational_centers={x["name"]:x["center"] for x in specs},
                  rows=len(extra),added_variables=0,added_products=0,
                  max_rows=max_rows,candidates_before_cap=len(choices),
                  squares=specs,skipped=skipped,
                  proof="Each row is (n*linear-m)^2 divided by a positive integer.",
                  height_credit="none; only a new exact complete certificate earns credit")
    return extra,manifest


def replay_moment_square_cuts(vs, rows, manifest):
    """Rebuild frozen squares directly; independently reject a new monomial."""
    vs=tuple(vs)
    if manifest.get("schema")!="rho5.cqg.moment-square-cuts.v1":
        raise ValueError("unknown square-cut manifest schema")
    specs=manifest["squares"]
    if len(specs)>40 or len(specs)!=manifest["rows"]:
        raise ValueError("invalid frozen square count")
    old=_quadratic_dictionary(vs,rows)
    result=[];names=set()
    for spec in specs:
        if spec["name"] in names:
            raise ValueError("duplicate frozen square name")
        names.add(spec["name"])
        center=s.Rational(spec["center"])
        poly,divisor=_primitive_square(vs,spec["direction"],center)
        if divisor!=spec["primitive_divisor"]:
            raise ValueError("primitive scaling mismatch")
        if not {m for m,_ in poly.terms() if sum(m)==2}<=old:
            raise ValueError("frozen square requires an absent monomial")
        result.append((spec["name"],poly))
    return result
