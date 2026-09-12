"""Bounded symbolic identity/size audit; run on X, not a height search.

Usage: python audit_packet_lift.py --output audit.json
Keeps Round43's original klo-dependent constants, only changes k upper root
to 11/5 for the audit's newly declared closed midband.
"""
import argparse
import json
from pathlib import Path
import sys
import sympy as s

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from round43_model_frozen import model
from packet_lift import packet_lift


def audit():
    results = []
    for case in ("I", "II", "III"):
        original_vs, _, original_rows, lo, hi, _ = model(s.Rational(21,10),case,True)
        hi[0] = s.Rational(11,5)
        for shape, minors, incidence in (
            ("tail","none","none"),
            ("tail","all","none"),
            ("tail","all","all"),
            ("bottom","all","all"),
            ("full","anchor","anchor"),
            ("full","all","none"),
            ("full","all","all"),
        ):
            vs, rows, lower, upper, result = packet_lift(
                original_vs, original_rows, lo, hi,
                shape=shape, minors=minors, incidence=incidence)
            lookup = {str(v):v for v in vs}
            definitions = {
                lookup[z]:s.sympify(e, locals=lookup)
                for z,e in result["definitions"].items()
            }
            for old, new in zip(original_rows,rows):
                assert old[0] == new[0]
                assert s.expand(old[1].as_expr()-new[1].as_expr()) == 0
            for name, poly in rows[len(original_rows):]:
                assert s.expand(poly.as_expr().subs(definitions,simultaneous=True)) == 0,name
            assert all(a <= b for a,b in zip(lower,upper))
            assert len(vs) == len(lower) == len(upper)
            if shape == "full":
                assert upper[vs.index(lookup["X00"]) ] < 0
                yl, yu = (a[vs.index(lookup["Y00"])] for a in (lower,upper))
                assert (yl > 0) if case == "I" else (yu < 0)
            result.update(head_case=case, k_interval=["21/10","11/5"],
                          identity_audit="PASS", original_rows_preserved=True)
            results.append(result)
    return {
        "status":"R44_PACKET_LIFT_IDENTITY_AND_SIZE_AUDIT_PASS",
        "scope":"Polynomial identities and dimension audit; no infeasibility certificate.",
        "configurations":results,
    }


if __name__ == "__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--output",type=Path)
    args=ap.parse_args()
    report=audit()
    encoded=json.dumps(report,indent=2)+"\n"
    if args.output:
        args.output.write_text(encoded)
    else:
        print(encoded,end="")
