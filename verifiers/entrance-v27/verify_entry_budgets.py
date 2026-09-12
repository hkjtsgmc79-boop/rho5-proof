"""Exact checks of V27's elementary uniform entry budgets.
Analytic sign-case proofs are in the report. Finite tests do not replace them.
"""
import json
from pathlib import Path
from fractions import Fraction as Q
import sympy as S
from v27_exact import *

a,b,c,d,z,w=S.symbols('a b c d z w')
lhs=a*c*(S.Rational(9,4)-(1+z-w))
rhs=(a*c*(z-S.Rational(1,2))**2+(b*c-z)*a*d+z*(a*d-z)
     +z*z*(1-a*c)+a*c*(1+w-b*d))
assert S.expand(lhs-rhs)==0

counts=dict(physical_states=0,sign_rectangle_instances=0,
            nonnegative_cross_core_instances=0,uniform_four_exit_instances=0,
            nine_quarters_core_instances=0)

def check_budgets(M):
    s=extract(M); complete_pivots(M)
    counts['physical_states']+=1
    for i in range(3):
        for j in range(3):
            if s['beta']*s['u'][i]*s['x'][i] <= 0 and -s['e']*s['vv'][j]*s['qq'][j] <= 0:
                req(abs(s['D'][i][j])<=2,'Uniform sign-rectangle lemma')
                counts['sign_rectangle_instances']+=1
    cross=s['D'][0][2]*s['D'][2][0]
    if cross>=0:
        req(s['r']<=s['k'],'Nonnegative-cross core bound')
        req(s['F']<=2*s['k'],'Two times k bound')
        counts['nonnegative_cross_core_instances']+=1
    if left_gate(s)[0]<=0 and right_gate(s)[0]<=0 and cross>=0:
        req(s['k']<=2 and s['F']<=4,'Uniform FOUR exit')
        counts['uniform_four_exit_instances']+=1
    req(s['F']<=Q(9,4)*s['k'],'Complete-pivot X-core 9/4 bound')
    counts['nine_quarters_core_instances']+=1

for f in (Q(1653,400),Q(206625837,50000000)):
    M=high_regression_seed(f)
    for trans in (False,True):
        for _,N in gauges(transpose(M) if trans else M):
            check_budgets(N)

low=small_example(u=[Q(-1,4),Q(1,4),Q(1,10)],residual=True)
check_budgets(low)
s=extract(low)
sharp=rebuild(s,k=Q(1,4),r=Q(3,8),w=Q(-3,16),
              A=Q(-1,4),B=Q(-1,8),c=Q(1),d=Q(1,2))
check_budgets(sharp)
req(extract(sharp)['F']==Q(9,4)*extract(sharp)['k'],'Sharp 3x3 core budget example')
strict=diagonal_contract(sharp,Q(1,100))
check_budgets(strict); complete_pivots(strict,strict_first_three=True)
t=extract(strict)
req(is_generic(t) and is_macro_r22(t) and residual_cell(t)==(1,1),'Strict residual opposite-core witness')
req(t['D'][0][2]*t['D'][2][0]<0,'Opposite-core phase')
req(t['F']==Q(84681,160000) and t['F']<4,'Not a high counterexample')
Path('strict_opposite_core_low_witness.json').write_text(json.dumps({
    'label':'LOW_HEIGHT_STRICT_RESIDUAL_EXAMPLE_NOT_ALPHA_COUNTEREXAMPLE',
    'F':str(t['F']),'cell':[1,1],
    'M':[[str(x) for x in row] for row in strict],
    'left_gate':[str(x) for x in left_gate(t)],
    'right_gate':[str(x) for x in right_gate(t)],
    'core_cross':str(t['D'][0][2]*t['D'][2][0])},indent=2)+'\n')

out={'status':'PASS','extra_symbolic_identities':1,'counts':counts,
     'scope':'uniform budgets proven analytically; finite tests and a LOW-height residual example only'}
Path('entry_budget_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
