"""Exact complete 5x5 M -> canonical 22-variable X source, using Fraction.

No optimizer, floating point, symbolic solve, or saved parameter dictionary is
used.  Matrix entries, Schur complements and diagonal signs are the source.
"""
from fractions import Fraction as Q


VARIABLE_NAMES = ('k','r','w','A','B','c','d','p','e','be',
                  'u0','u1','u2','x0','x1','x2','v0','v1','v2','q0','q1','q2')


def rational(value):
    if isinstance(value, (float, bool)):
        raise ValueError('Matrix entries must be exact rational strings or integers')
    return Q(value)


def parse_matrix(value):
    if len(value) != 5 or any(len(row) != 5 for row in value):
        raise ValueError('Expected a 5x5 matrix')
    return [[rational(z) for z in row] for row in value]


def schur(matrix):
    pivot = matrix[0][0]
    if not pivot:
        raise ValueError('Zero pivot in the declared actual source')
    return [[matrix[i][j]-matrix[i][0]*matrix[0][j]/pivot
             for j in range(1,len(matrix))] for i in range(1,len(matrix))]


def diagonal_conjugate(matrix, signs):
    if len(signs) != len(matrix) or any(z not in (-1,1) for z in signs):
        raise ValueError('Invalid actual simultaneous row/column signs')
    return [[signs[i]*matrix[i][j]*signs[j] for j in range(len(matrix))]
            for i in range(len(matrix))]


def transpose_control(matrix):
    """The actual J M.T J, J=diag(1,-1,1,1,1), preserving symmetric H."""
    return diagonal_conjugate([list(row) for row in zip(*matrix)], (1,-1,1,1,1))


def extract(matrix):
    if matrix[0][0] != 1:
        raise ValueError('Declared X source must have M00=1')
    st, D = schur(matrix), None
    p = st[0][0]
    if p <= 0:
        raise ValueError('Expected positive actual pivot p')
    D = schur(st)
    k = D[0][0]
    if k <= 0:
        raise ValueError('Expected positive actual pivot k')
    H = schur(D)
    r,w = H[0][0],H[1][1]
    if r <= 0 or H[0][1] != r or H[1][0] != r:
        raise ValueError('Actual tail is not [[r,r],[r,w]] with r>0')
    u = [matrix[i+2][0] for i in range(3)]
    x = [st[i+1][0]/p for i in range(3)]
    v = matrix[0][2:]
    q = st[0][1:]
    values = [k,r,w,D[0][1],D[0][2],D[1][0]/k,D[2][0]/k,
              p,-matrix[0][1],matrix[1][0]] + u+x+v+q
    point = dict(zip(VARIABLE_NAMES,values))
    reconstructed = reconstruct(point)
    if reconstructed != matrix:
        raise AssertionError('Same-source reconstruction mismatch')
    return point, (st,D,H)


def reconstruct(a):
    k,r,w,A,B,c,d,p,e,be = (a[z] for z in VARIABLE_NAMES[:10])
    u,x,v,q = ([a[f'{name}{i}'] for i in range(3)] for name in ('u','x','v','q'))
    D = [[k,A,B],[c*k,r+c*A,r+c*B],[d*k,r+d*A,w+d*B]]
    return [[Q(1),-e,*v],
            [be,p-e*be,*[q[j]+be*v[j] for j in range(3)]]] + [
                [u[i],p*x[i]-e*u[i],
                 *[D[i][j]+x[i]*q[j]+u[i]*v[j] for j in range(3)]]
                for i in range(3)]


def physical_audit(matrix):
    point,(st,D,H) = extract(matrix)
    bands=[]
    for label,block,width in (('M',matrix,Q(1)),('first_schur',st,point['p']),
                              ('D',D,point['k']),('H',H,point['r'])):
        slacks=[(f'{label}_{i}{j}',width-abs(z))
                for i,row in enumerate(block) for j,z in enumerate(row)]
        failed=[(name,str(z)) for name,z in slacks if z<0]
        if failed:
            raise AssertionError(f'Physical bands failed: {failed}')
        name,minimum=min(slacks,key=lambda t:t[1])
        bands.append({'layer':label,'absolute_bands':len(slacks),
                      'minimum_slack':str(minimum),'minimum_at':name})
    F=point['r']-point['w']
    if F<0 or abs(point['w'])>point['r']:
        raise AssertionError('Tail pivot qualification failed')
    if schur(H)[0][0] != -F:
        raise AssertionError('Actual final pivot mismatch')
    return point,{'status':'EXACT_FULL_PHYSICAL_X_PASS', 'bands':bands,
                  'tail_shape':'[[r,r],[r,w]]', 'same_source_reconstruction':True,
                  'pivots':list(map(str,(Q(1),point['p'],point['k'],point['r'],-F))),
                  'F':str(F)}


def normalize(matrix):
    """Canonical e,beta>0,x0>0,q0<0,A<=0, with actual sign operations."""
    current=[list(row) for row in matrix]
    total=[1]*5
    operations=[]

    def flip(label,signs):
        nonlocal current,total
        current=diagonal_conjugate(current,signs)
        total=[a*b for a,b in zip(total,signs)]
        operations.append({'name':label,'diagonal':list(signs)})

    original,_=extract(current)
    if original['k']<=2:
        raise ValueError('This regression normalization requires k>2')
    if original['e']<0:
        flip('positive_e_beta',(1,-1,1,1,1))
    point,_=extract(current)
    if point['x0']<0:
        flip('positive_x0_negative_q0',(1,1,-1,-1,-1))
    point,_=extract(current)
    if point['A']>0:
        flip('head_preserving_nonpositive_A',(1,1,1,-1,-1))
    point,physical=physical_audit(current)
    if not (point['e']>0 and point['be']>0 and point['x0']>0
            and point['q0']<0 and point['A']<=0):
        raise AssertionError('Canonical sign qualification failed')
    if current != diagonal_conjugate(matrix,total):
        raise AssertionError('Recorded actual diagonal map mismatch')
    for n in ('p','k','r','w'):
        if point[n]!=original[n]:
            raise AssertionError('Sign normalization changed a pivot')
    b,h=point['p']*point['x0'],-point['q0']
    if b>=1 and h>=1:
        case='I'; expected=(1,1)
    elif b>=1 and h<=1:
        case='II'; expected=(1,-1)
    elif b<=1 and h>=1:
        case='III'; expected=(-1,1)
    else:
        raise AssertionError('Forbidden head case IV at k>2')
    if not (expected[0]*point['u0']>0 and expected[1]*point['v0']>0):
        raise AssertionError('Head case and actual receiver signs disagree')
    return current,point,case,{'operations':operations,'combined_diagonal':total,
                               'head_case':case,'b':str(b),'h':str(h),
                               'physical':physical}
