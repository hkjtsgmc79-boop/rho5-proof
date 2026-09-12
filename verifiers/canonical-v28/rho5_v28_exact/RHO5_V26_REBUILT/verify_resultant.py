import json
from pathlib import Path
import sympy as s

DATA = json.loads(Path("alpha.json").read_text(encoding="utf-8"))
co = [s.Integer(x) for x in DATA["minimal_polynomial"]["coefficients_ascending"]]

x,e = s.symbols("s epsilon")
L=(2-x)*(1+x)
d=2*x*(1-x)-e*L
B=2*x**2+e*L
Yn=x*(1-x)*(1-e)+e**2*L
Yd=x*(1-x)
Vn=2*x**2*(1-x)-2*e*d-e*B*x*(1-x)+e**2*B*L
Vd=2*x**2*(1-x)

G=s.expand(
    (2*d*(1-e)-e**2*L**2)*Yn*Vn
    -d*(2-2*x+e*L)*Yd*Vn
    -4*d*x**4*(1-x)*Yn
)
assert s.Poly(G,x,e).degree(x)==10
assert s.Poly(G,x,e).degree(e)==7

res=s.resultant(G,s.diff(G,x),x)
assert s.degree(res,e)==109
P=sum(co[i]*(4+2*e)**i for i in range(len(co)))
pref=e**34*(e-2)*(e-1)**2*(e+1)**7*(e**2-2*e+2)**2
assert s.expand(131072*res-pref*P)==0

print("RESULTANT_P61_IDENTITY_PASSED")
