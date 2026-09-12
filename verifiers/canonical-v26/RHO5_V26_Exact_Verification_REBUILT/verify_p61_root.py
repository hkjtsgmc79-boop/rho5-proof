from fractions import Fraction as Q
from math import comb
import json
from pathlib import Path

DATA = json.loads(Path("alpha.json").read_text(encoding="utf-8"))
coeff = [int(x) for x in DATA["minimal_polynomial"]["coefficients_ascending"]]

fminus = Q(4132517, 10**6)
fplus = Q(103313, 25000)
alo = Q(DATA["isolating_interval"]["lower"])
ahi = Q(DATA["isolating_interval"]["upper"])

def horner(co, x):
    y = Q(0)
    for c in reversed(co):
        y = y*x + c
    return y

def derivative(co):
    return [i*co[i] for i in range(1, len(co))]

def compose_affine_power(co, a, d):
    # p(a+d*t) in power basis t^k.
    n = len(co)-1
    out = [Q(0) for _ in range(n+1)]
    for i,c in enumerate(co):
        for k in range(i+1):
            out[k] += Q(c) * comb(i,k) * a**(i-k) * d**k
    while len(out)>1 and out[-1]==0:
        out.pop()
    return out

def power_to_bernstein(power):
    n = len(power)-1
    return [
        sum(power[k] * Q(comb(i,k), comb(n,k)) for k in range(i+1))
        for i in range(n+1)
    ]

assert fminus < alo < ahi < fplus
assert horner(coeff, fminus) < 0
assert horner(coeff, fplus) > 0

dco = derivative(coeff)
power = compose_affine_power(dco, fminus, fplus-fminus)
bern = power_to_bernstein(power)
assert len(bern) == 61
assert all(x > 0 for x in bern)

print("P61_ROOT_CERTIFICATE_PASSED")
print("bernstein_coefficients:", len(bern), "all_strictly_positive")
