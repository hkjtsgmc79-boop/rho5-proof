"""R44 rational same-source regression. Run on X; no discovery or optimizer.

The contradiction row F>=GAMMA and all target-dependent root boxes are NOT
requirements on the two true lower-height control matrices.
"""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sympy as s
from exact_x_source import (VARIABLE_NAMES,parse_matrix,physical_audit,
                            normalize,transpose_control)

HERE=Path(__file__).resolve().parent
DEFAULT_PROJECT=HERE.parents[2]
WITNESSES=('exact_core_block_witness.json','exact_nearpeak_nowall.json')
EXPECTED_WITNESS_SHA256={
    'exact_core_block_witness.json':'0fefb028b5f99b8b4689d1f92e0f62aa64001d40d3967363835d9af03cd7a348',
    'exact_nearpeak_nowall.json':'9ec62c0d18ca27aa15d7b68e2aa51fcbde997ac97ceebdbe7becc3df358b21b6',
}


def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def recorded_path(path,project):
    """Prefer portable package-relative provenance, preserving outside paths."""
    resolved=Path(path).resolve()
    try:
        return resolved.relative_to(project).as_posix()
    except ValueError:
        return str(resolved)


def qvalue(value):
    return Q(int(value.p),int(value.q))


def evaluate(poly,values):
    answer=Q(0)
    for exponents,coefficient in poly.terms():
        term=qvalue(coefficient)
        for value,exponent in zip(values,exponents):
            if exponent:
                term*=value**exponent
        answer+=term
    return answer


def check_rows(rows,vs,point,*,zero=False):
    values=[point[str(v)] for v in vs]
    slacks=[(name,evaluate(poly,values)) for name,poly in rows]
    failures=[{'name':name,'slack':str(z)} for name,z in slacks if (z!=0 if zero else z<0)]
    if failures:
        raise AssertionError(json.dumps({'failed_rows':failures[:12]},indent=2))
    minimum=min(slacks,key=lambda t:t[1]) if slacks else (None,Q(0))
    return {'status':'EXACT_ZERO_PASS' if zero else 'EXACT_NONNEGATIVE_PASS',
            'rows':len(rows),'minimum_slack':str(minimum[1]),'minimum_at':minimum[0],
            'zero_rows':sum(z==0 for _,z in slacks),
            'slacks':{name:str(z) for name,z in slacks}}


def generic_physical_box(vs,K,case):
    """A deliberately broad canonical box, independent of F>=GAMMA."""
    J=Q(9,4)
    bounds={
        'k':(K,J),'r':(Q(0),Q(4)),'w':(-J,Q(4)),
        'A':(-J,Q(0)),'B':(-J,J),'c':(-Q(1),Q(1)),'d':(-Q(1),Q(1)),
        'p':(Q(1),Q(2)),'e':(Q(0),Q(1)),'be':(Q(0),Q(1)),
    }
    for i in range(3):
        for n in ('u','x','v'):
            bounds[f'{n}{i}']=(-Q(1),Q(1))
        bounds[f'q{i}']=(-Q(2),Q(2))
    bounds['x0']=(K/2-1,Q(1))
    bounds['q0']=(-Q(2),2-K)
    su=1 if case in ('I','II') else -1
    sv=1 if case in ('I','III') else -1
    for name,sign in (('u0',su),('v0',sv)):
        bounds[name]=(K-2,Q(1)) if sign==1 else (-Q(1),2-K)
    return ([s.Rational(str(bounds[str(z)][0])) for z in vs],
            [s.Rational(str(bounds[str(z)][1])) for z in vs])


def model_families(project,K,case,modules):
    builder,roots,rectangles,lifts,anchor_link=modules
    vs,_,base,_,_,gamma=builder.model(s.Rational(str(K)),case,True)
    if tuple(map(str,vs))!=VARIABLE_NAMES:
        raise AssertionError('Unexpected base variable order')
    retained=[(name,poly) for name,poly in base if name!='F']
    if len(retained)!=len(base)-1:
        raise AssertionError('Expected exactly one contradiction target row F')
    lo,hi=generic_physical_box(vs,K,case)
    head,_,_=roots.augment_model(vs,[],lo,hi,s.Rational(str(K)),s.Rational(9,4),case)
    chsh={str(normalize):rectangles.rankone_rectangle_rows(vs,case,'all',normalize)
          for normalize in (False,True)}
    anchor_vs=tuple(vs)+(s.Symbol('G'),)
    anchor_g=s.Rational(str(4*(K-2)))
    anchor_rows=anchor_link.anchor_tail_projected_rows(
        anchor_vs,case,anchor_g,include_plain=True)
    if len(anchor_rows)!=32:
        raise AssertionError('Expected 16 projected and 16 plain anchor-tail rows')
    _,anchor_source,_,_,_=anchor_link.anchor_tail_expressions(anchor_vs,case)
    anchor=(anchor_vs,anchor_rows,anchor_g,s.Poly(anchor_source,*anchor_vs))
    packets=[]
    for shape,minor,incidence in (
            ('tail','all','none'),('tail','all','all'),('bottom','all','all'),
            ('full','anchor','anchor'),('full','all','none'),('full','all','all')):
        pvs,prows,plo,phi,manifest=lifts.packet_lift(
            vs,[],lo,hi,shape=shape,minors=minor,incidence=incidence)
        packets.append((pvs,prows,plo,phi,manifest))
    return vs,retained,head,chsh,packets,lo,hi,qvalue(gamma),anchor


def audit_source(path,project,K,modules,cache,with_transpose):
    raw=path.read_bytes()
    data=json.loads(raw)
    M=parse_matrix(data['matrix'])
    raw_point,physical=physical_audit(M)
    if 'k' in data and Q(data['k'])!=raw_point['k']:
        raise AssertionError('Saved k disagrees with actual matrix')
    F=raw_point['r']-raw_point['w']
    if 'F' in data and Q(data['F'])!=F:
        raise AssertionError('Saved F disagrees with actual matrix')
    controls=[('canonical_original',M)]
    if with_transpose:
        T=transpose_control(M)
        tp,_=physical_audit(T)
        if any(tp[n]!=raw_point[n] for n in ('p','k','r','w')):
            raise AssertionError('Actual transposition changed a pivot')
        controls.append(('canonical_actual_transpose',T))
    result={'input':recorded_path(path,project),'sha256':sha256(raw).hexdigest(),'physical_original':physical,
            'input_authority':'matrix only; saved parameter values are not model inputs',
            'representations':[]}
    for label,matrix in controls:
        normalized,point,case,norm=normalize(matrix)
        if not (K<=point['k']<=Q(9,4)):
            raise AssertionError('Requested K does not cover this true source')
        if case not in cache:
            cache[case]=model_families(project,K,case,modules)
        vs,base,head,chsh,packets,lo,hi,gamma,anchor=cache[case]
        if any(not (qvalue(a)<=point[str(v)]<=qvalue(b)) for v,a,b in zip(vs,lo,hi)):
            raise AssertionError('Canonical source escaped the F-independent physical box')
        record={'name':label,'normalization':norm,
                'normalized_matrix':[[str(z) for z in row] for row in normalized],
                'variables_22':{name:str(point[name]) for name in VARIABLE_NAMES},
                'K':str(K),'gamma':str(gamma),'F':str(F),'F_minus_gamma':str(F-gamma),
                'target_row_F_tested':False,
                'target_dependent_root_membership_tested':False,
                'physical_packet_box_membership':'EXACT_PASS',
                'base_non_target':check_rows(base,vs,point),
                'new_head_rows':check_rows(head,vs,point),
                'chsh':{flag:check_rows(rows,vs,point) for flag,rows in chsh.items()},
                'packets':[]}
        p,k=point['p'],point['k']
        G={'I':point['e']*point['be'],'II':point['e']*point['u0'],
           'III':point['be']*point['v0']}[case]
        exact_product_slack=G*(p+1-k)-(p-1)**2
        if p+1-k<=0 or exact_product_slack<0:
            raise AssertionError('Actual nonlinear common G budget failed')
        record['actual_common_G']={'G':str(G),'p_plus_one_minus_k':str(p+1-k),
                                   'nonlinear_slack':str(exact_product_slack)}
        anchor_vs,anchor_rows,anchor_g,anchor_source=anchor
        anchor_point={**point,'G':G}
        g=qvalue(anchor_g)
        if not (0<=g<=G<=1):
            raise AssertionError('True head anchor does not satisfy 0<=4(K-2)<=G<=1')
        if evaluate(anchor_source,[anchor_point[str(z)] for z in anchor_vs])!=G:
            raise AssertionError('Anchor module source differs from actual type-specific G')
        record['anchor_tail']={
            'g':str(g),'G_actual':str(G),'G_minus_g':str(G-g),
            'true_source_binding':str(anchor_source.as_expr()),
            'uses_target_root':False,
            **check_rows(anchor_rows,anchor_vs,anchor_point)}
        for pvs,prows,plo,phi,manifest in packets:
            packet_point=dict(point)
            for symbol in pvs[len(vs):]:
                name=str(symbol);i,j=int(name[1]),int(name[2])
                a,b=('x','q') if name[0]=='X' else ('u','v')
                packet_point[name]=point[f'{a}{i}']*point[f'{b}{j}']
            if any(not (qvalue(a)<=packet_point[str(v)]<=qvalue(b))
                   for v,a,b in zip(pvs,plo,phi)):
                raise AssertionError('Actual packet escaped its F-independent lifted box')
            checked=check_rows(prows,pvs,packet_point,zero=True)
            record['packets'].append({
                'shape':manifest['shape'],'minors':manifest['minors'],
                'incidence':manifest['incidence'],'identities':checked['rows'],
                'status':checked['status'],'actual_lift_values':{
                    str(v):str(packet_point[str(v)]) for v in pvs[len(vs):]}})
        result['representations'].append(record)
    return result


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--project-root',type=Path,default=DEFAULT_PROJECT)
    ap.add_argument('--code-root',type=Path,
                    help='Round44 code directory; defaults to PROJECT/work/round44_midband. Explicit paths resolve from the working directory.')
    ap.add_argument('--input-dir',type=Path,
                    help='Two frozen control JSONs; defaults to PROJECT/outputs/knowledge_import_r2_20260908. Explicit paths resolve from the working directory.')
    ap.add_argument('--klo',default='41/20')
    ap.add_argument('--no-transpose-controls',action='store_true')
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    project=args.project_root.resolve()
    code_root=(args.code_root or project/'work/round44_midband').resolve()
    input_dir=(args.input_dir or project/'outputs/knowledge_import_r2_20260908').resolve()
    K=Q(args.klo)
    if not (2<K<=Q(9,4)):
        raise ValueError('Require 2<K<=9/4')
    dependencies=(
        ('r44_regression_base',code_root/'round43_model_frozen.py'),
        ('r44_regression_roots',code_root/'roots/augment_midband_roots.py'),
        ('r44_regression_rectangles',code_root/'tail_coupling/rankone_rectangle_rows.py'),
        ('r44_regression_packets',code_root/'lift/packet_lift.py'),
        ('r44_regression_anchor_tail',code_root/'tail_coupling/head_anchor_tail_link.py'),
    )
    modules=tuple(load_module(name,path) for name,path in dependencies)
    cache={}
    results=[audit_source(input_dir/name,project,K,modules,cache,
                         not args.no_transpose_controls) for name in WITNESSES]
    for result in results:
        if EXPECTED_WITNESS_SHA256[Path(result['input']).name]!=result['sha256']:
            raise AssertionError('Frozen imported source hash mismatch')
    provenance={'frozen_import_hashes_checked':True,
                'expected_sha256':EXPECTED_WITNESS_SHA256,
                'source':'Hashes transcribed from the preserved R2 import manifest; no third input JSON required.'}
    cases=sorted({r['normalization']['head_case'] for z in results for r in z['representations']})
    output={'schema':'rho5.cqg.r44.actual-matrix-regression.v1',
            'status':'R44_EXACT_SAME_SOURCE_MATRIX_REGRESSION_PASS','K':str(K),
            'scope':'Finite rational regression of physical matrices and all applicable new rows; no continuous-domain bound.',
            'head_cases_present':cases,'head_cases_not_exercised':sorted(set(('I','II','III'))-set(cases)),
            'target_policy':'F>=gamma omitted; neither original nor augmented target-dependent root boxes are tested.',
            'layout':{'relative_path_base':'project-root',
                      'code_root':recorded_path(code_root,project),
                      'input_dir':recorded_path(input_dir,project)},
            'source_provenance':provenance,
            'code_sha256':{recorded_path(path,project):sha256(path.read_bytes()).hexdigest()
                           for path in [*(path for _,path in dependencies),
                                        HERE/'exact_x_source.py',Path(__file__).resolve()]},
            'witnesses':results}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'status':output['status'],'sources':len(results),
                      'representations':sum(len(z['representations']) for z in results),
                      'head_cases_present':cases,'output':str(args.output)}))


if __name__=='__main__':
    main()
