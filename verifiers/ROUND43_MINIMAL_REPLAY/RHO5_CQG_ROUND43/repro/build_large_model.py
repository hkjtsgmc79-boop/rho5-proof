"""Fresh complete X-chart necessary system for the large-pivot interval.

Inherited mathematical inputs: real rho3=9/4, rho4=4, and pk<=4.
No V31 small-pivot sign ordering or root is imported.
"""
from pathlib import Path
import argparse, json, math
import sympy as s

def model(klo,head_case=None,head_loss=False,root_grid=10**9):
    k,r,w,A,B,c,d,p,e,be=s.symbols('k r w A B c d p e be')
    u=s.symbols('u0:3');x=s.symbols('x0:3');v=s.symbols('v0:3');q=s.symbols('q0:3')
    vs=(k,r,w,A,B,c,d,p,e,be)+u+x+v+q
    D=s.Matrix([[k,A,B],[c*k,r+c*A,r+c*B],[d*k,r+d*A,w+d*B]])
    rows=[]
    def band(value,bound,label):
        rows.extend([(label+'+',bound-value),(label+'-',bound+value)])
    band(e,1,'e');band(be,1,'beta');band(p-e*be,1,'head')
    for i in range(3):
        band(u[i],1,'u'+str(i));band(x[i],1,'x'+str(i))
        band(v[i],1,'v'+str(i));band(q[i],p,'q'+str(i))
        band(p*x[i]-e*u[i],1,'L'+str(i));band(q[i]+be*v[i],1,'P'+str(i))
        for j in range(3):
            band(D[i,j],k,f'D{i}{j}')
            stage=D[i,j]+x[i]*q[j]
            band(stage,p,f'S{i}{j}');band(stage+u[i]*v[j],1,f'O{i}{j}')
    f=s.Rational(4132517,1000000)
    rows.extend([('F',r-w-f),('Fcore',s.Rational(9,4)*k-r+w),('r+w',r+w),
                 ('det3',4-p*k),('plower',4*p-r+w),('k_step',2*p-k),('r_step',2*k-r),('w_plus_k',w+k),('rAc',k-A-r),
                 ('head_parabola',3*p-p*p-k),('stage_parabola',3*p*k-k*k-p*r),('core_parabola',2*k*r-r*r+k*w)])
    if head_case:
        su=1 if head_case in ('I','II') else -1
        sv=1 if head_case in ('I','III') else -1
        rows.extend([('receiver_u',2+(2-p)*su*u[0]-k),('receiver_v',2+(2-p)*sv*v[0]-k),
                     ('head_b_case',(p*x[0]-1)*(1 if head_case in ('I','II') else -1)),
                     ('head_h_case',(-q[0]-1)*(1 if head_case in ('I','III') else -1))])
    K=s.Rational(9,4)
    rad=K-klo; n=math.isqrt(int(s.ceiling(rad*10**8)))
    if s.Rational(n*n,10**8)<rad:n+=1
    width=s.Rational(n,10000)
    pmax=min(4/klo,s.Rational(3,2)+width)
    pmin=max(f/4,klo/2,s.Rational(3,2)-width)
    lower=[klo,f/2,-K,-K,-K,-1,-1,pmin,pmin-1,pmin-1,
           -1,-1,-1,klo/pmax-1,-1,-1,-1,-1,-1,-pmax,-pmax,-pmax]
    upper=[K,4,4-f,0,K,1,1,pmax,1,1,1,1,1,1,1,1,1,1,1,pmax-klo,pmax,pmax]
    if head_case:
        receiver_min=(klo-2)/(2-pmin)
        for idx,sgn in ((10,su),(16,sv)):
            if sgn==1:lower[idx]=receiver_min
            else:upper[idx]=-receiver_min
        if head_case in ('I','II'):lower[13]=max(lower[13],1/pmax)
        else:upper[13]=min(upper[13],1/pmin)
        if head_case in ('I','III'):upper[19]=min(upper[19],-1)
        else:lower[19]=max(lower[19],-1)
        if head_loss:
            a0=receiver_min;b0=pmin-1
            deficit=K-klo
            b=p*x[0];h=-q[0];S0=k+x[0]*q[0];O0=S0+u[0]*v[0]
            delta=3*p-p*p-k
            rows.extend([('cross_head_u',2+(u[0]-be)*(-v[0])-k),
                         ('cross_head_v',2+(v[0]-e)*(-u[0])-k)])
            if head_case=='I':
                loss=1-O0+a0*(e*u[0]-b+1+be*v[0]-h+1)+a0*a0*(1-e*be)+(2-pmax)*(2*p-b-h)
                lower[13]=max(lower[13],(1+a0)/pmax)
                upper[19]=min(upper[19],-1-a0)
                tail_loss=deficit/(2-pmax)
                lower[13]=max(lower[13],1-tail_loss/pmin)
                upper[19]=min(upper[19],-pmin+tail_loss)
                lower[8]=max(lower[8],1-deficit/(a0*a0))
                lower[9]=max(lower[9],1-deficit/(a0*a0))
                g0=1-deficit/(a0*a0)
                if g0>0:
                    upper[10]=min(upper[10],(pmax-1+deficit/a0)/g0)
                    upper[16]=min(upper[16],(pmax-1+deficit/a0)/g0)
                rows.extend([('mixed_head_gap_Iu',be-u[0]-k+2),('mixed_head_gap_Iv',e-v[0]-k+2)])
            elif head_case=='II':
                loss=(p-1)*(be-p+1)+(1-h+be*v[0])+b0*(1-O0+u[0]*v[0]-v[0])+(1-x[0])*h
                rows.append(('mixed_receiver',2+(u[0]-be)*(-v[0])-k))
                rows.append(('mixed_head_gap',u[0]-be-k+2))
                upper[9]=min(upper[9],pmax-1+deficit/b0)
                lower[10]=max(lower[10],1-deficit/(b0*a0))
                lower[13]=max(lower[13],1-deficit/(klo-pmax))
                lower[8]=max(lower[8],b0*b0/(b0*b0+deficit))
                lower[19]=max(lower[19],-1+b0*a0)
            else:
                loss=(p-1)*(e-p+1)+(1-b+e*u[0])+b0*(1-O0+u[0]*v[0]-u[0])+p*x[0]+x[0]*q[0]
                rows.append(('mixed_receiver',2+(v[0]-e)*(-u[0])-k))
                rows.append(('mixed_head_gap',v[0]-e-k+2))
                upper[8]=min(upper[8],pmax-1+deficit/b0)
                lower[16]=max(lower[16],1-deficit/(b0*a0))
                upper[19]=min(upper[19],-pmin*max(0,1-deficit/(klo-pmax)))
                lower[9]=max(lower[9],b0*b0/(b0*b0+deficit))
                upper[13]=min(upper[13],(1-b0*a0)/pmin)
            rows.append(('common_head_loss',delta-loss))
    rows=[(n,s.Poly(t,*vs)) for n,t in rows if t!=0]
    # Exact outward rounding keeps the C++ root literals small.
    if root_grid:
        lower=[s.Rational(s.floor(s.Rational(t)*root_grid),root_grid) for t in lower]
        upper=[s.Rational(s.ceiling(s.Rational(t)*root_grid),root_grid) for t in upper]
    else:lower,upper=list(map(s.Rational,lower)),list(map(s.Rational,upper))
    return vs,D,rows,lower,upper,f

def export(klo,out,head_case=None,head_loss=False):
    vs,D,rows,lo,hi,f=model(klo,head_case,head_loss);nv=len(vs)
    mons=sorted({mon for _,poly in rows for mon,_ in poly.terms() if sum(mon)==2})
    pairs=[[i for i,power in enumerate(mon) for _ in range(power)] for mon in mons]
    pos={mon:nv+i for i,mon in enumerate(mons)}
    scale=math.lcm(*(int(c.q) for _,poly in rows for _,c in poly.terms()))
    den=math.lcm(*(int(x.q) for x in lo+hi))
    output=[]
    for name,poly in rows:
        coeff=[s.Rational(0)]*(nv+len(pairs));rhs=s.Rational(0)
        for mon,c in poly.terms():
            deg=sum(mon)
            if deg==0:rhs=c
            elif deg==1:coeff[mon.index(1)]=-c
            elif deg==2:coeff[pos[mon]]=-c
            else:raise AssertionError('Nonquadratic')
        ints=[int(scale*c) for c in coeff];rr=int(scale*rhs)
        divisor=math.gcd(*ints,rr)
        output.append(dict(name=name,coefficients=[t//divisor for t in ints],rhs=rr//divisor,
                           row_divisor=divisor,row_multiplier=str(s.Rational(scale,divisor)),polynomial=str(poly.as_expr())))
    roots=[[int(den*x) for x in a] for a in (lo,hi)]
    integers=[scale,den]+[t for row in roots for t in row]+[r['rhs'] for r in output]+[t for r in output for t in r['coefficients']]
    assert all(abs(t)<2**63 for t in integers),'Exact model literal exceeds int64; reduce the rational root denominators.'
    data=dict(schema='rho5.cqg.large-direct.quadratic.v1',variables=list(map(str,vs)),target=str(f),
              klo=str(klo),head_case=head_case,head_loss=head_loss,base_multiplier=scale,root_denominator=den,root_numerators=roots,pairs=pairs,rows=output)
    out.mkdir(parents=True,exist_ok=True)
    (out/'model.json').write_text(json.dumps(data,indent=2)+'\n')
    header=['#pragma once','#include <vector>','#include <utility>',f'constexpr int EV={nv}, EN={nv+len(pairs)}, EB={len(rows)};',
            f'constexpr long long BASE_SCALE={scale}, ROOT_DEN={den};',
            'inline const std::vector<std::pair<int,int>> epairs={'+','.join('{%s,%s}'%tuple(ij) for ij in pairs)+'};',
            'inline const std::vector<std::vector<long long>> ebase={'+','.join('{'+','.join(map(str,r['coefficients']))+'}' for r in output)+'};',
            'inline const std::vector<long long> erhs={'+','.join(str(r['rhs']) for r in output)+'};',
            'inline const std::vector<long long> erow_divisor={'+','.join(str(r['row_divisor']) for r in output)+'};',
            'inline const std::vector<long long> erootlo={'+','.join(map(str,roots[0]))+'};',
            'inline const std::vector<long long> eroothi={'+','.join(map(str,roots[1]))+'};']
    (out/'mc_exact_model.hpp').write_text('\n'.join(header)+'\n')
    floats=['#pragma once','#include "mc_exact_model.hpp"',
            'constexpr int NV=EV, NX=EN;',
            'inline const auto pairs=epairs;',
            'inline const std::vector<std::vector<double>> base=[](){std::vector<std::vector<double>> a;for(size_t i=0;i<ebase.size();i++){std::vector<double> v;for(auto z:ebase[i])v.push_back(double(z)*erow_divisor[i]/BASE_SCALE);a.push_back(v);}return a;}();',
            'inline const std::vector<double> rhs=[](){std::vector<double> v;for(size_t i=0;i<erhs.size();i++)v.push_back(double(erhs[i])*erow_divisor[i]/BASE_SCALE);return v;}();']
    (out/'mc_model.hpp').write_text('\n'.join(floats)+'\n')
    vendor=Path(__file__).resolve().parent/'vendor'
    kern=(vendor/'mc_exact_kernel.hpp').read_text().replace('Big(4800)','Big(ROOT_DEN)')
    (out/'mc_exact_kernel.hpp').write_text(kern)
    (out/'mc_simplex_dual.hpp').write_bytes((vendor/'mc_simplex_dual.hpp').read_bytes())
    verify=(vendor/'mc_verify.cpp').read_text().replace('visit(', 'r43_visit_node(').replace('V31_SMALL_PIVOT_GLOBAL_EXACT_PASS','R43_LARGE_PIVOT_INTERVAL_EXACT_PASS')
    (out/'mc_verify.cpp').write_text(verify)
    src=(vendor/'mc_certify.cpp').read_text().replace('1600.', '(double(BASE_SCALE)/erow_divisor[i])').replace('if(solves%10000==0)', 'if(solves%1000==0)').replace('nodes>2000000','nodes>NODE_LIMIT')
    src=src.replace('long nodes=0','long NODE_LIMIT=200000;\nlong nodes=0')
    begin=src.index('int main(')
    src=src[:begin]+'''int main(int argc,char**argv){try{
 if(argc<2)throw std::runtime_error("usage: certify OUTPUT [NODE_LIMIT]");
 if(argc>2)NODE_LIMIT=std::stol(argv[2]); std::ofstream out(argv[1]);if(!out)throw std::runtime_error("open failed");
 start=std::chrono::steady_clock::now();refine(root_box(),out);out.flush();
 double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
 std::cout<<"EXACT_GENERATION_DONE nodes="<<nodes<<" leaves="<<leaves<<" maxdepth="<<maxdepth<<" seconds="<<sec<<" open=0"<<std::endl;
 }catch(const std::exception&e){std::cerr<<"FAIL "<<e.what()<<std::endl;return 1;}}
'''
    (out/'mc_certify.cpp').write_text(src)
    print(json.dumps(dict(out=str(out),variables=nv,products=len(pairs),rows=len(rows),target=str(f),klo=str(klo),scale=scale,den=den)))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('klo');ap.add_argument('output');ap.add_argument('--head-case',choices=['I','II','III']);ap.add_argument('--head-loss',action='store_true');a=ap.parse_args()
    export(s.Rational(a.klo),Path(a.output),a.head_case,a.head_loss)
