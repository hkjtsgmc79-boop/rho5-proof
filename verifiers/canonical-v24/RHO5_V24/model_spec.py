from fractions import Fraction as F
from pathlib import Path
import sympy as s,json
Q=s.Rational
NAMES='t E beta V T X Y Z delta gamma nu k a b r p g j h v q Ah Br u1'.split()
ROOT=[('15/32','1'),('1/64','1/2'),('1/8','7/8'),('0','1'),('1/16','7/8'),('45/64','1'),('0','1'),('1/2','1'),('1/8','1'),('0','1'),('1/16','1'),('33/16','9/4'),('0','3/2'),('1','9/4'),('33/16','9/4'),('17/16','15/8'),('1/8','15/16'),('3/16','1'),('1/16','1'),('0','7/8'),('1/16','1'),('0','1'),('1/16','1/4'),('0','1')]
def system(stage,middle,first):
 vs=s.symbols(' '.join(NAMES)); t,E,be,V,T,X,Y,Z,de,ga,nu,k,a,b,r,p,g,j,h,v,q,Ah,Br,u1=vs
 d=t*X-Y;ta=Y-X*V;De=Z-T*X;mu=V*Z-T*Y;Om=t*De+E*ta-mu
 o00=k-X*j-g;o20=-E*k-Z*j-T*g;o01=-a-X+de*h;o21=r+E*a-Z-nu*h
 eq=[('def_delta',de-1+be*X),('def_gamma',ga-V+be*Y),('def_nu',nu-be*Z+T),('L2_one',p*Z-1-T),('O10',t*k-Y*j-V*g-1),('O11',r-t*a-Y+ga*h-1),('O02',-b+X*q+v+1),('O12',r-t*b+Y*q+V*v-1),('O22',1-r+E*b+Z*q+T*v)]
 eq += [('stage',k-X*j-p)] if stage=='X' else [('stage',t*k-Y*j-p)]
 eq += [('middle',1-a-X+de*h)] if middle=='1' else [('middle',r+E*a-Z-nu*h-1)]
 eq += [('P0minus',j+be*g-1)] if first=='P' else [('O20eq',E*k+Z*j+T*g-1)]
 z=1-q-be*v;G=g-v
 eq += [('head_middle',T*(1-h)-(r-2)-E*a-(1-o21)-Z*(p-1-be*h)),('tail_moment',(t-V)*v+d*q-(r-1-t)),('cofactor_moment',mu*G-(Y+Z)*(r-2)-(t*Z+Y*E)*(k-b)-Y*(1+o20)),('tail_beta',E*b-(r-2)-(1-Z)-Z*z-nu*v),('first_o00_moment',mu*(1-o00)-(De+ta)*(r-2)-Om*(k-b)-ta*(1+o20))]
 if first=='P':eq += [('Bfirst',t*k-1-Y-ga*g),('Btail_g',ga*G-(r-2)-t*(k-b)+Y*z),('Btail_nu',nu*G-(r-2)-E*(k-b)-(1+o20)-Z*z)]
 if stage=='Y':eq += [('stage_g',V*g-p+1)]
 else:eq += [('stage_g',t*p-1-V*g+d*j)]
 ins=[('target',800*r-1653),('d',d),('r0',Q(33,16)-1-t-d),('rho',t*p+d-1),('tau',ta),('Delta_gap',De-ta-Q(1,32)),('mu',mu),('tVgap',48*(t-V)-1),('ell',nu-E*de),('zeta',t*nu-E*ga),('P0lower',1-j-be*g),('b_k',k-b),('t_E',t-E),('g_v',G),('P2upper',z),('g_height',3-r-g),('O00height',3-r-o00),('F_beta',5-2*r-be),('beta_lower',be-Q(1,8)),('v_stage',p-1-v),('O20lower',1+o20),('O01lower',1+o01),('O21upper',1-o21),('S01lower',p-a-X-(1-de)*h),('q1stage',p-1-be*h),('D21core',k-r-E*a),('a_k',k-a),('headp',1+be-p),('L1upper',1-p*Y+V),('L0upper',2-p*X),('W',3-r-2*E-T),('kprefix',3-be-k),('rmiddle',2+be-T-r),('kjoint',1+(p-1)+X*(1-be*(p-1))-k),('Ek',1-T-E*k),('xdisc',16*X**2-17*X+4),('ksquare',X*(1+X-k)+Q(1,4)),('middle_nu',nu*h-(r-2)-E*a),('mid_a',t*a-(r-2)),('k_r',k-r),('vpos',v)]
 # General common middle budget consequences, retaining O01 slack u1.
 eq += [('def_Ah',Ah-de*h),('def_Br',Br-(r-2)-E*a),('def_u1',u1-1+a+X-de*h)]
 L=1+Br-X
 ins += [('mid_h_budget',h*(be-(p-1))-Br),('mid_h_stage',p-1+u1-h),('L_budget',de*(p-1)-L),('Br_core',k-2-Br),('Ah_square',(1+X*u1)**2-4*X*Ah-4*X**2*Br),('Ah_second',Ah-4*X*Ah*L-4*X**2*Br*L),('Ah_combined',(1+X*u1)**2*(1-4*X*L)-4*X**2*Br)]
 if middle=='1':ins += [('X_four_fifths',5*X-4)]

 # V23 representative tail disjunction, kept as an exact polynomial equation.
 eq += [('tail_endpoint_union',z*(k-b)),('tail_cofactor_exact',mu+De+ta+Om*b-(De+ta)*r)]
 if first=='P':
  NC=p*ga+(X if stage=='X' else Y)*(V+be)
  DC=ga+be*t*X if stage=='X' else t*V
 else:
  NC=p*mu+(X if stage=='X' else Y)*(V+T)
  DC=mu+X*(V*E+T*t) if stage=='X' else V*(t*Z+E*Y)
 eq += [('first_capacity_exact',DC*k-NC),('mid_spread',r-1-Y-t*(1-X)-(t*de-ga)*h+t*u1)]
 ins += [('first_stage_order',(p*(X-Y)-d*k) if stage=='X' else (d*k-p*(X-Y))),('middle_corner_core',k-(1+Z+nu*h))] if middle=='2' else [('first_stage_order',(p*(X-Y)-d*k) if stage=='X' else (d*k-p*(X-Y)))]
 # all remaining semantic bands (some duplicate but useful in contracted form)
 D=s.Matrix([[k,-a,-b],[t*k,r-t*a,r-t*b],[-E*k,r+E*a,-r+E*b]])
 xs=[X,Y,Z];us=[1,V,T];vv=[-g,h,v];qq=[-j,-1-be*h,q]
 for J in range(3):
  for I in range(3):
   S=D[I,J]+xs[I]*qq[J];O=S+us[I]*vv[J]
   for name,pol in [('S+',p-S),('S-',p+S),('O+',1-O),('O-',1+O),('D+',k-D[I,J]),('D-',k+D[I,J])]:
    if pol!=0:ins += [(f'{name}{I}{J}',pol)]
 return vs,eq,ins

def spec(stage,middle,first):
 vs,eq,ins=system(stage,middle,first);nodes=[];cache={}
 for i,x in enumerate(vs):cache[x]=i;nodes.append([0,i,0,0])
 def add(x):
  x=s.sympify(x)
  if x in cache:return cache[x]
  if x.is_Rational:
   val=F(int(x.p),int(x.q))*(1<<32)
   if val.denominator!=1:raise ValueError(x)
   ix=len(nodes);nodes.append([1,0,0,val.numerator]);cache[x]=ix;return ix
  if x.is_Add or x.is_Mul:
   op=2 if x.is_Add else 3;ts=[add(a)for a in x.args];cur=ts[0]
   for nxt in ts[1:]:ix=len(nodes);nodes.append([op,cur,nxt,0]);cur=ix
   cache[x]=cur;return cur
  if x.is_Pow and x.exp.is_Integer and x.exp>=0:
   if x.exp==0:return add(1)
   ts=[add(x.base)]*int(x.exp);cur=ts[0]
   for nxt in ts[1:]:ix=len(nodes);nodes.append([3,cur,nxt,0]);cur=ix
   cache[x]=cur;return cur
  raise ValueError(x)
 roots=[[add(e),1,n]for n,e in eq]+[[add(e),0,n]for n,e in ins]
 base_count=len(nodes)
 gradrefs=[[add(s.diff(e,x)) for x in vs] for _,e in eq+ins]
 return dict(schema='RHO5-V24-Exceptional-Wall-Contact-v1',stage=stage,middle=middle,first=first,precision=32,base_count=base_count,gradrefs=gradrefs,variables=NAMES,nodes=nodes,roots=roots,root_box=[[int(F(a)*(1<<32)),int(F(b)*(1<<32))]for a,b in ROOT],equalities=[[n,str(s.expand(e))]for n,e in eq],nonnegative=[[n,str(s.expand(e))]for n,e in ins])
def write_cpp(sp,path):
 ss=['static const std::vector<Node> spec={']+['{%d,%d,%d,%dLL},'%tuple(n)for n in sp['nodes']]+['};','static const std::vector<std::pair<int,int>> roots={']+['{%d,%d},'%tuple(n[:2])for n in sp['roots']]+['};','static const std::array<I,NV> ROOT={']+['I(%dLL,%dLL),'%tuple(n)for n in sp['root_box']]+['};'];ss += [f'static constexpr int BASE_COUNT={sp["base_count"]};','static const std::vector<std::array<int,NV>> gradrefs={'] + ['{'+','.join(map(str,row))+'},'for row in sp['gradrefs']]+['};'];Path(path).write_text('\n'.join(ss)+'\n')
if __name__=='__main__':
 for first,stage in [('P','X'),('P','Y'),('E','X')]:
  for middle in '12':
   key=first+stage+middle;sp=spec(stage,middle,first);Path('certificates/'+key+'.json').write_text(json.dumps(sp,indent=2)+'\n');write_cpp(sp,'cpp/'+key+'.hpp');print(key,len(sp['nodes']),len(sp['equalities']),len(sp['nonnegative']))
