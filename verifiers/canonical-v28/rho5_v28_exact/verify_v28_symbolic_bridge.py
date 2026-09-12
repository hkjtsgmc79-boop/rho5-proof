from pathlib import Path
import sys,re
import sympy as s
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE/'RHO5_V26_REBUILT'))
import guard_system as g
from localization_exact_core import guards_generic
# The shared C++ expression DAG is interpreted symbolically here, independently
# of compiled interval execution, then compared to the retained 37 polynomials.
text=(BASE/'guards.hpp').read_text(); env={'r':g.f/2}
env.update(dict(zip(['beta','V','ss','Y','Z','v'],g.variables)))
for line in text.splitlines():
    line=line.strip()
    if line.startswith('auto ') and 'x[' not in line:
        name,expr=line[5:].rstrip(';').split('=',1);env[name.strip()]=s.sympify(expr,locals=env)
ret=text.split('return {',1)[1].split('};',1)[0]
cpp=[s.sympify(z.strip(),locals=env) for z in ret.split(',')]
py0,py35,py36=guards_generic(list(g.variables),g.f)
original=g.guards+[g.g35,g.g36]
assert len(cpp)==len(original)==37
for i,(a,b,c) in enumerate(zip(cpp,original,py0+[py35,py36])):
    assert s.expand(a-b)==0,('cpp/report dictionary',i)
    assert s.expand(a-c)==0,('cpp/rational dictionary',i)
# Parametric polynomial identities used for full-height transport and strict
# head margins in the bridge proof (not merely fixed-f numerical checks).
be,V,ss,Y,Z,v,h,b,R=s.symbols('beta V ss Y Z v h b R')
eps=R-1;r=R+1;p=1+ss;T=p*Z-1;q=1-be*v;ga=V-be*Y;nu=be*Z-T;mu=V*Z-T*Y
A=R+Y+ga*v;C=R-Z+nu*v;W=R*(Y+Z)+mu*v;N=V*(Y+Z)+ss*mu
lam=N/(V*W);j=(lam*A-p)/Y;g0=ss/V;a=b*(R-Y+ga*h)/A
Pcal=eps*V*((Y+Z)-v*(nu-ga))-(ss-V*v)*(mu+R*(nu-ga))
aa=R*(1+q)+V*v;cc=V+be*R;B0=2+(1-be)*v;X=(b-1-v)/q;E=C/b
O01=-a-X*(1+be*h)+h;S01=-a-X*(1+be*h);O21=r+E*a-Z*(1+be*h)+T*h
checks={
 'Pcal_head_slack':Pcal-V*W*(1-j-be*g0),
 'G5_original_slack':A*(B0+(1+be)*h)-b*(aa+cc*h)-A*q*(1+O01),
 'G6_stage_slack':A*(p*q+(1+v)*(1+be*h))-b*(aa+cc*h)-A*q*(p+S01),
 'G7_bottom_slack':(mu+R*(nu-ga))*h-A*(R-Z)-C*(R-Y)-A*(1-O21),
 'middle_equal_receivers':(A*(B0+(1+be)*h)-b*(aa+cc*h))-(A*(p*q+(1+v)*(1+be*h))-b*(aa+cc*h))-A*q*(h-ss),
}
for label,expr in checks.items():assert s.cancel(expr)==0,label
# Same-old-head transport: (t*delta-gamma)*v = R+Y-t(1+X).
t,XX,de,v0,RR=s.symbols('t XX delta v0 RR')
expr=t*(1+XX+de*v0)-(RR+Y+ga*v0)
assert s.expand(expr-((t*de-ga)*v0-(RR+Y-t*(1+XX))))==0
print('V28_SYMBOLIC_BRIDGE_PASS', '37 guards x 2 dictionaries;',len(checks)+1,'parametric identities')
