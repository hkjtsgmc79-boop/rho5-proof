"""Independent conditional safety rules, NOT frozen V44 terminal labels.

Premise: the input encloses the same complete physical B states, with F the
actual final height. This module does not establish source membership or
physical existence. verify_all.py supplies that provenance separately.
All unproved branches remain OPEN; a zero multiplier never proves F <= alpha.
"""
from fractions import Fraction as Q
from itertools import product
from exact_interval import I,serial,rational
ORDER='k r s t A B c d p e beta u0 u1 u2 x0 x1 x2 v0 v1 v2 q0 q1 q2 F'.split()
GAMMA=Q(4132517,10**6)

def image(aux):
    if len(aux)!=24:raise ValueError('Need complete B24 enclosure')
    return dict(zip(ORDER,[I(*x)for x in aux]))

def transpose(x):
    if x['p'].lo<=0 or x['k'].lo<=0:raise ValueError('Positive pivot denominator required')
    y=x.copy(); y['e'],y['beta']=x['beta'],x['e']
    for i in range(3):
        y[f'u{i}'],y[f'v{i}']=x[f'v{i}'],x[f'u{i}']
        y[f'x{i}'],y[f'q{i}']=-x[f'q{i}']/x['p'],-x['p']*x[f'x{i}']
    y['A'],y['B'],y['c'],y['d']=x['c']*x['k'],x['d']*x['k'],x['A']/x['k'],x['B']/x['k']
    y['s'],y['t']=x['t'],x['s'];return y

def diagonal_swap(x):
    y=x.copy()
    for w in ('u','x'):y[w+'1'],y[w+'2']=-x[w+'2'],x[w+'1']
    for w in ('v','q'):y[w+'1'],y[w+'2']=x[w+'2'],-x[w+'1']
    y['c'],y['d'],y['A'],y['B']=-x['d'],x['c'],x['B'],-x['A']
    y['s'],y['t']=x['t'],x['s'];return y

def sign_rep(x,sgn):
    e1,e2,e3=sgn;y=x.copy()
    for n in ('e','beta'):y[n]=e1*x[n]
    for w in ('u','v'):
        y[w+'0']=e2*x[w+'0']
        for j in (1,2):y[w+str(j)]=e3*x[w+str(j)]
    for w in ('x','q'):
        y[w+'0']=e1*e2*x[w+'0']
        for j in (1,2):y[w+str(j)]=e1*e3*x[w+str(j)]
    for n in ('A','B','c','d'):y[n]=e2*e3*x[n]
    return y

def representations(x):
    for t,d in product((0,1),repeat=2):
        y=transpose(x)if t else x
        if d:y=diagonal_swap(y)
        for ss in product((-1,1),repeat=3):
            yield 'T%dD%dS%s'%(t,d,''.join('+'if v==1 else'-'for v in ss)),sign_rep(y,ss)

def b09_components(x):
    a=x['x2']-x['d']*x['x0'];b=x['c']*x['x0']-x['x1'];z=a+b
    m=a*x['u1']+b*x['u2'];n=x['u0']*(a*x['c']+b*x['d'])-m
    guards={'u0':x['u0'],'x2':x['x2'],'u2':x['u2'],'b':b,'a_minus_b':a-b,'z':z,'M':m,'N':n}
    strict={'u0','x2','z'}
    opposite=[g for g,v in guards.items()if v.hi<0 or(g in strict and v.hi<=0)]
    uncertain=[g for g,v in guards.items()if v.lo<0 or(g in strict and v.lo<=0)]
    return a,b,z,m,n,guards,opposite,uncertain

def old_budget(x,alpha,kind='B09',C=Q(1)):
    alpha=rational(alpha);C=rational(C)
    if C<=0:raise ValueError('Strictly positive C required')
    if kind not in ('B09','B10_MINUS','B10_PLUS'):raise ValueError('Unknown budget')
    a,b,z,m,n,g,op,unc=b09_components(x)
    result={'rule':kind,'qualification':g,'strict_guards':['u0','x2','z'],'opposite':op,'not_certified':unc}
    if unc:return {**result,'status':'OPEN_QUALIFICATION','height_tested':False}
    d0=x['u0']*x['x2']*z
    if d0.lo<=0:raise ArithmeticError('Positive multiplier not certified')
    un=2*(d0+x['x2']*m+n*(1+x['u2']))
    vn=1+x['u2']-x['x2'];qn=(x['d']-x['c'])*(1+x['u2'])*x['u0']+(x['u1']-x['u2'])*vn+x['beta']*z*vn
    hn=x['u1']-x['u2']+x['beta']*z;jn=hn+(x['d']-x['c'])*x['u0']
    if kind=='B09':mult=d0;num=un;extra={}
    elif kind=='B10_MINUS':
        extra={'2aC-1':2*a*C-1,'2MC-Hn':2*m*C-hn,'2NC+Jn':2*n*C+jn,'(a-b)C-1':(a-b)*C-1}
        mult=C*d0;num=C*un+d0+qn
    else:
        extra={'2bC-1':2*b*C-1,'2MC+Hn':2*m*C+hn,'2NC-Jn':2*n*C-jn}
        mult=C*d0;num=C*un+d0-qn
    if any(v.lo<0 for v in extra.values()):
        return {**result,'extra_qualification':extra,'status':'OPEN_COEFFICIENT','height_tested':False}
    ar=alpha*mult-num;gr=GAMMA*mult-num
    status='GAMMA_EXCLUDED'if gr.lo>0 else'ALPHA_SAFE'if ar.lo>=0 else'OPEN_HEIGHT'
    return {**result,'extra_qualification':extra,'status':status,'height_tested':True,'positive_multiplier':mult,'height_numerator':num,'alpha_residual':ar,'gamma_residual':gr,'conditional_on_complete_physical_B':True}

def signed_circuit_budgets(x,alpha):
    """Two independent all-sign circuits; eight finite cone candidates.
    Absolute coefficients are exact piecewise bounds, including zero weights.
    B09/B10 remain available and are not claimed to be subsumed numerically.
    """
    alpha=rational(alpha);result=[]
    for level in ('RAW','STAGE'):
        if level=='RAW':
            w=[x[f'u{i}']-x['beta']*x[f'x{i}']for i in range(3)]
            A=w[2]-x['d']*w[0];B=x['c']*w[0]-w[1]
        else:A=x['x2']-x['d']*x['x0'];B=x['c']*x['x0']-x['x1']
        K=A*x['c']+B*x['d']
        J=A*x['x1']+B*x['x2']-K*x['x0'] if level=='RAW'else I(0)
        cost=abs(A)+abs(B)+abs(K)+abs(J)if level=='RAW'else x['p']*(abs(A)+abs(B)+abs(K))
        for col,sgn in product(('FIRST','SECOND'),(-1,1)):
            aa,bb=sgn*A,sgn*B
            z=aa+bb if col=='FIRST'else aa-bb
            balance=aa-bb if col=='FIRST'else -bb-aa
            row={'rule':level+'_CIRCUIT','column':col,'sign':sgn,'normal':[aa,bb],'anchor_coefficient':sgn*K,'raw_second_row_coefficient':sgn*J,'cost':cost,'qualification':{'positive_height_multiplier':z,'nonnegative_tail_coefficient':balance}}
            if z.lo<=0 or balance.lo<0:
                row.update(status='OPEN_QUALIFICATION',height_tested=False)
            else:
                ar=alpha*z-2*cost;gr=GAMMA*z-2*cost
                row.update(status='GAMMA_EXCLUDED'if gr.lo>0 else'ALPHA_SAFE'if ar.lo>=0 else'OPEN_HEIGHT',height_tested=True,alpha_residual=ar,gamma_residual=gr)
            result.append(row)
    low=[x['x1']-x['c']*x['x0'],x['x2']-x['d']*x['x0'],x['u1']-x['c']*x['u0'],x['u2']-x['d']*x['u0']]
    result.append({'rule':'INHERITED_LEFT_RANK_ONE','zero_identities':low,'status':'GAMMA_EXCLUDED'if all(v.is_zero()for v in low)else'OPEN_QUALIFICATION','height_cap':'4'if all(v.is_zero()for v in low)else None})
    return result
