#!/usr/bin/env python3
"""V35 low-r alpha-localization model. Source inequalities are necessary at F>=gamma.
A complete proof may use contradiction leaves and source-conditioned alpha-safe leaves.
No root is complete until its entire original-root partition is paid.
"""
from pathlib import Path
import importlib.util,json,math,argparse
import sympy as s
ROOT=Path(__file__).resolve().parent
R=s.Rational
# The endpoint K=2 is used only as a CLOSED OUTER bound for actual k>2 sources.
# All formulae are division-free there, and every source still has k>2.
def base_module():
    src=(ROOT/'reference/r45_build_model.py').read_text()
    old='assert 2<K<=J<=R(43,20)'
    assert src.count(old)==1
    namespace={'__name__':'v34_endpoint_extended_base','__file__':str(ROOT/'reference/r45_build_model.py')}
    exec(compile(src.replace(old,'assert 2<=K<=J<=R(43,20)'),namespace['__file__'],'exec'),namespace)
    return namespace
BASE=base_module()

def encode(vs,polys):
    rr=[(label,s.Poly(s.expand(expr),*vs)) for label,expr in polys]
    rr=[(label,p) for label,p in rr if not p.is_zero]
    monos=sorted({m for _,p in rr for m,_ in p.terms() if sum(m)==2})
    pairs=[[i for i,a in enumerate(m) for _ in range(a)] for m in monos]
    pos={m:len(vs)+i for i,m in enumerate(monos)}
    rows=[]
    for label,p in rr:
        co=[s.S(0)]*(len(vs)+len(monos));rhs=s.S(0)
        for m,val in p.terms():
            d=sum(m)
            if d==0:rhs=val
            elif d==1:co[m.index(1)]=-val
            elif d==2:co[pos[m]]=-val
            else:raise ValueError('nonquadratic row '+label)
        den=math.lcm(*[int(z.q) for z in co+[rhs]])
        vals=[int(z*den) for z in co+[rhs]];g=math.gcd(*vals);vals=[v//g for v in vals]
        if max(map(abs,vals))>=2**62:raise ValueError('row coefficient outside frozen format')
        rows.append({'name':label,'coefficients':vals[:-1],'rhs':vals[-1],
                     'polynomial':str(p.as_expr()),'positive_scale':str(R(den,g))})
    return pairs,rows

def make_model(K,J,typ,branch='low'):
    K,J=R(K),R(J)
    if not (2<=K<J<=R(21,10)):raise ValueError('V35 range requires 2 <= K < J <= 2.1')
    data=BASE['make_model'](K,J,typ,True,False)
    vs=tuple(s.Symbol(n) for n in data['variables']);env=dict(zip(data['variables'],vs))
    data['source_version']='V35_ALPHA_LOCALIZATION_2026-09-08'
    data['branch']=branch
    data['actual_k_gt_2']=True
    if branch=='low':
        data['actual_r_relation']='r<=k (including equality)'
        import hashlib
        cert=ROOT/'local_wall_certificate.json';alpha=ROOT/'alpha.json'
        data['proof_goal']='F<=exact_alpha; target is a LOWER localization trigger, never a claimed uniform gamma cap'
        data['alpha_ports_certificate_sha256']=hashlib.sha256(cert.read_bytes()).hexdigest()
        data['alpha_definition_sha256']=hashlib.sha256(alpha.read_bytes()).hexdigest()
        data['legal_safe_terminal_codes']={'0':'local_flow_0','1':'local_flow_1','2':'local_flow_2','3':'local_flow_3','4':'weak_R0','5':'2r<=alpha_lower'}
        return data
    raise ValueError('V35 only freezes the low-r scope; high-r inputs are reviewed, not rerun')

def headers(data,path):
    BASE['headers'](data,path)
    from alpha_ports import write_header
    write_header(data,Path(path))
    with (Path(path)/'mc_exact_model.hpp').open('a') as f:
        f.write('constexpr int HEAD_TYPE='+str(1 if data['type']=='I' else 2)+';\n')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--K',required=True);ap.add_argument('--J',required=True)
    ap.add_argument('--type',required=True,choices=['I','II']);ap.add_argument('--branch',choices=['low'],required=True)
    ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    data=make_model(a.K,a.J,a.type,a.branch);headers(data,a.out)
    (a.out/'scope.json').write_text(json.dumps({k:data[k] for k in ('K','J','type','branch','target','actual_k_gt_2','actual_r_relation')},indent=2)+'\n')
    print(json.dumps({'scope':json.loads((a.out/'scope.json').read_text()),'variables':len(data['variables']),'products':len(data['pairs']),'rows':len(data['rows'])}))
if __name__=='__main__':main()
