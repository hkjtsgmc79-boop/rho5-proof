"""Exact dictionary between the eight-contact carrier and the resultant polynomial."""
import sympy as s
x,e=s.symbols('s epsilon');L=(2-x)*(1+x)
be=x+e*L/(2*x);v=x*(be-x)/(1-be);b=2+x*(be-x);a=(1-be)*x;r=2+e
Y=1-e*(x-v)/(x+v);V=1-e*(2+be*(x-v))/(x+v)
E=(e+(be-x)*v)/b
checks={
 'tail_scale':b-2-(1-be)*v,
 'core_contact':b-r-E*a,
 'middle_top':-a-1-be*x+x+1,
 'middle_receiver_equations':r-a-Y+(V-be*Y)*x-1,
 'tail_receiver_equations':r-b+Y*(1-be*v)+V*v-1,
 'bottom_middle':r+E*a-1-be*x+x*x-1,
 'bottom_tail':-r+E*b+1-be*v+x*v+1,
}
for name,z in checks.items():assert s.cancel(z)==0,name
D=2*x*(1-x)-e*L;B=2*x*x+e*L
Yn=x*(1-x)*(1-e)+e*e*L;Yd=x*(1-x)
Vn=2*x*x*(1-x)-2*e*D-e*B*x*(1-x)+e*e*B*L;Vd=2*x*x*(1-x)
assert s.cancel(Y-Yn/Yd)==0
assert s.cancel(V-Vn/Vd)==0
G=(2*D*(1-e)-e*e*L*L)*Yn*Vn-D*(2-2*x+e*L)*Yd*Vn-4*D*x**4*(1-x)*Yn
res=e+(be-x)*v+(b-1-x)/Y+x*x/V-1
assert s.cancel(res+G/(2*D*Yn*Vn))==0
# Forward positive-denominator elimination of beta from two tail/core contacts.
beta=s.symbols('beta');d=beta-x
forward=(2+x*d)*(x*d-e)-(1-beta)*x*e-x*x*d*d
assert s.expand(forward-(2*x*(beta-x)-e*L))==0
print('V28_CONTACT_CARRIER_DICTIONARY_PASS',len(checks)+4,'identities')
