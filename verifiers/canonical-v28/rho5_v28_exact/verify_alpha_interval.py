import json
from fractions import Fraction as Q
from pathlib import Path
p=json.loads((Path(__file__).resolve().parent/'RHO5_V26_REBUILT/alpha.json').read_text())
co=list(map(int,p['minimal_polynomial']['coefficients_ascending']))
def evaluate(x):
    v=Q(0)
    for c in reversed(co):v=v*x+c
    return v
lo=Q(p['isolating_interval']['lower']);hi=Q(p['isolating_interval']['upper'])
assert lo<hi and evaluate(lo)<0<evaluate(hi)
print('V28_FULL_DECIMAL_ISOLATING_INTERVAL_EXACT_SIGNS_PASS')
