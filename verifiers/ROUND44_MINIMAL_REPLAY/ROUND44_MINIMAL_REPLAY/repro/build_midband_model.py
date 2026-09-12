"""Fresh Round44 necessary system on a closed k interval, under F>=gamma.

The counterexample inequality is a proof target, not an assumed upper bound.
Every original variable and complete D/S/O band stays in the same source.
"""
from pathlib import Path
import argparse, json
import sympy as s
import round43_model_frozen as frozen
from roots.augment_midband_roots import augment_model, head_product_lower, DEFAULT_LAMBDAS
from tail_coupling.rankone_rectangle_rows import rankone_rectangle_rows
from tail_coupling.head_anchor_tail_link import anchor_tail_projected_rows, head_anchor_tail_lift
from tail_coupling.moment_square_cuts import moment_square_cuts
from lift.packet_lift import packet_lift

base_model=frozen.model


def model(klo,khi,head_case,rectangles='tail',lift='none',plo=None,phi=None,root_grid=10**9,rbranch='all',head_lift=False,anchor_tail='none',stage_anchor=False,fold_i=False,moment_cuts='none',manifest_out=None):
    K,J=map(s.Rational,(klo,khi))
    vs,D,rows,lo,hi,gamma=base_model(K,head_case,True,root_grid=None)
    if plo is not None:lo[7]=max(lo[7],s.Rational(plo))
    if phi is not None:hi[7]=min(hi[7],s.Rational(phi))
    rows,lo,hi=augment_model(vs,rows,lo,hi,K,J,head_case,root_grid=root_grid)
    if fold_i:
        assert head_case=='I','Only head case I is fixed by the actual transpose.'
        rows.append(('I_transpose_half_u_ge_v',s.Poly(vs[10]-vs[16],*vs)))
    k,r,w=vs[:3]
    if rbranch=='low':
        rows.append(('r_branch_low',s.Poly(k-r,*vs)))
        hi[1]=min(hi[1],J);hi[2]=min(hi[2],J-gamma)
    elif rbranch=='high':
        # Covers strict r>k; r=k is paid by the low branch.
        rows.append(('r_branch_high_closure',s.Poly(r-k,*vs)))
        lo[1]=max(lo[1],K);hi[4]=min(hi[4],0)
        lo[5]=max(lo[5],0);lo[6]=max(lo[6],0)
        A,B,c,d=vs[3:7]
        for name,expr in [('B_gap',k-B-r),('c_gap',k*(1+c)-r),('d_gap',k*(1+d)-r),
                          ('B_bottom_gap',2*k-r+w-B),('core_product_db',-J*d*B-(r-k)**2),
                          ('core_product_ca',-J*c*A-(r-k)**2)]:
            rows.append(('high_r_'+name,s.Poly(expr,*vs)))
    if head_lift:
        G=s.Symbol('G');vs=tuple(vs)+(G,)
        rows=[(name,s.Poly(poly.as_expr(),*vs)) for name,poly in rows]
        p,e,be=vs[7:10];u=vs[10];v=vs[16]
        actual={'I':e*be,'II':e*u,'III':be*v}[head_case]
        lo.append(max(4*(K-2),head_product_lower(K,lo[7],hi[7])));hi.append(s.Rational(1))
        extra=[('definition_plus',G-actual),('definition_minus',actual-G),
               ('perspective',G*(p+1-k)-(p-1)**2),('prefix',G-p+1)]
        extra += [('lambda_'+str(i),G-(2*l-l*l)*(p-1)-l*l*(k-2)) for i,l in enumerate(DEFAULT_LAMBDAS)]
        rows += [('r44_head_G_'+name,s.Poly(expr,*vs)) for name,expr in extra]
    if anchor_tail!='none':
        assert head_lift,'The anchor-tail cuts require the actual G definition.'
        rows+=anchor_tail_projected_rows(vs,head_case,lo[vs.index(s.Symbol('G'))])
        if anchor_tail=='lift':
            vs,rows,lo,hi,_=head_anchor_tail_lift(vs,rows,lo,hi,head_case=head_case,root_grid=root_grid)
    if rectangles!='none':rows+=rankone_rectangle_rows(vs,head_case,rectangles,True)
    if stage_anchor and rectangles not in ('all','stage'):
        for name,poly in rankone_rectangle_rows(vs,head_case,'stage',True):
            pieces=name.split('_')
            if pieces[-3][0]=='0' and pieces[-2][0]=='0':
                rows.append(('head_'+name,poly))
    lift_manifest=None
    if lift!='none':
        vs,rows,lo,hi,lift_manifest=packet_lift(vs,rows,lo,hi,shape=lift,minors='all',incidence='all',root_grid=root_grid)
        p=vs[7]
        for z in vs[22:]:
            if str(z).startswith('X'):
                rows.extend([(f'actual_packet_width_{z}+',s.Poly(p-z,*vs)),(f'actual_packet_width_{z}-',s.Poly(p+z,*vs))])
    if moment_cuts!='none':
        extra,moment_manifest=moment_square_cuts(vs,rows,lo,hi,mode=moment_cuts)
        rows+=extra
        if manifest_out is not None:manifest_out['moment_manifest']=moment_manifest
    lo,hi=list(map(s.Rational,lo)),list(map(s.Rational,hi))
    assert all(a<=b for a,b in zip(lo,hi)),'Empty analytic root: record separately, do not export a reversed box.'
    return (vs,D,rows,lo,hi,gamma),lift_manifest


def export(args):
    extras={}
    result,lift_manifest=model(args.klo,args.khi,args.case,args.rectangles,args.lift,args.plo,args.phi,rbranch=args.rbranch,head_lift=args.head_lift,anchor_tail=args.anchor_tail,stage_anchor=args.stage_anchor,fold_i=args.fold_i,moment_cuts=args.moment_cuts,manifest_out=extras)
    saved=frozen.model
    frozen.model=lambda *a,**kw:result
    try:frozen.export(s.Rational(args.klo),args.output,args.case,True)
    finally:frozen.model=saved
    data=json.loads((args.output/'model.json').read_text())
    data.update(schema='rho5.cqg.round44.midband.v1',khi=str(s.Rational(args.khi)),
                rectangles=args.rectangles,lift=args.lift,lift_manifest=lift_manifest,rbranch=args.rbranch,head_lift=args.head_lift,anchor_tail=args.anchor_tail,stage_anchor=args.stage_anchor,fold_i=args.fold_i,
                moment_cuts=args.moment_cuts,moment_manifest=extras.get('moment_manifest'),
                p_slice=[args.plo,args.phi],scope='Declared canonical real X representative sector with counterexample F>=gamma; use the documented r/type/transpose coverage.')
    (args.output/'model.json').write_text(json.dumps(data,indent=2)+'\n')
    for name in ['mc_verify.cpp','mc_certify.cpp']:
        src=(args.output/name).read_text().replace('r43_visit_node','r44_visit_node').replace('R43_LARGE_PIVOT_INTERVAL_EXACT_PASS','R44_MIDBAND_INTERVAL_EXACT_PASS')
        (args.output/name).write_text(src)
    # Keep an inspectable model configuration with every new tree.
    print(json.dumps({'K':data['klo'],'J':data['khi'],'case':args.case,'rectangles':args.rectangles,'lift':args.lift,'rows':len(data['rows']),'variables':len(data['variables']),'products':len(data['pairs'])}))


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('klo');ap.add_argument('khi');ap.add_argument('case',choices=['I','II','III']);ap.add_argument('output',type=Path)
    ap.add_argument('--rectangles',choices=['none','tail','all','prefix','stage','core'],default='tail')
    ap.add_argument('--lift',choices=['none','tail','bottom','full'],default='none')
    ap.add_argument('--plo');ap.add_argument('--phi')
    ap.add_argument('--rbranch',choices=['all','low','high'],default='all')
    ap.add_argument('--head-lift',action='store_true')
    ap.add_argument('--anchor-tail',choices=['none','projected','lift'],default='none')
    ap.add_argument('--stage-anchor',action='store_true')
    ap.add_argument('--fold-I',dest='fold_i',action='store_true')
    ap.add_argument('--moment-cuts',choices=['none','minimal','core','head','balanced'],default='none')
    export(ap.parse_args())
