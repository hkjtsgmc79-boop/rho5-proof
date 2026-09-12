#!/usr/bin/env python3
"""Existing complete matrices: protect scope, reject the obsolete F<=4 claim."""
from __future__ import annotations
import json
from pathlib import Path
from fractions import Fraction as Q
from legacy_native_checker import native,build,blocks,residual,physical_slacks
ROOT=Path(__file__).resolve().parent

def main():
    matrices=json.loads((ROOT/'regression_matrices.json').read_text());results={}
    for name,M in matrices.items():
        st=native(M);pivots,stage=blocks(M)
        assert build(st)==[[Q(v) for v in row] for row in M]
        assert all(z>=0 for _,z in physical_slacks(st))
        F=abs(pivots[-1]);k=st['k'];H=residual(st)
        is_x=H[0][0]==H[0][1]==H[1][0] and H[0][0]>0
        if name in ('small_boundary','small_generic','crossing_generic','doubly_blocked'):
            assert is_x and k<=2 and 4<F<Q(1653,400)
        if name=='R0_near_alpha':assert is_x and k>2 and F>Q(1653,400)
        if name=='large_boundary':assert is_x and k>2
        if name=='proper_macro_B_near_alpha':assert not is_x and F>Q(1653,400)
        results[name]={'k':str(k),'F':str(F),'X_chart':is_x}
    print(json.dumps(dict(status='V31_SCOPE_AND_PHYSICAL_REGRESSIONS_PASS',complete_matrices=len(results),
                          obsolete_unconditional_4_cap_not_used=True,
                          high_R0_and_B_outside_scope_preserved=True)))
if __name__=='__main__':main()
