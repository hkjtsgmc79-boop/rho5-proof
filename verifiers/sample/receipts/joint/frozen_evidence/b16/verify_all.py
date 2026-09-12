#!/usr/bin/env python3
"""B16 independent source-bound certificate acceptance.
Rebuild exactly the selected depth-11/depth-14 canonical sources, not old S2,
not depth-19, and not the global root. No solver is imported by this entry.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse,copy,hashlib,json,sys,tempfile
ROOT=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.setrecursionlimit(10000)
sys.path.insert(0,str(ROOT/'support'))
from exact_interval import I
RULE='B16_CANONICAL_PREFIX_TWO_CHART_GAMMA_V1'
SEMANTICS='GAMMA_EXCLUDED_CANONICAL_SOURCE'
PARENT_SHA='9d7f10cf242dddc51c6fd5a03fed4adf9f4084bb9c3584e801f4693ce093f780'
PARTIAL_SHA='b4515303844ba40537cc083d7c6be71cce9f142d3bcbf9023ce2bbeb674988f7'
COVER='BETA_ONE_L1_MINUS_VS_L0_OR_L2_PLUS'
LABELS=('B1|N:L1-:L0+','B1|N:L1-:L2+')
ORDER='k r s t A B c d p e beta u0 u1 u2 x0 x1 x2 v0 v1 v2 q0 q1 q2 F'.split()
GAMMA=Q(4132517,10**6)
SPECS={'11': {'index': 435003, 'path': '10011101101', 'projection_raw_sha256': '51684d5336ffbce69e5e413ae7fe09285eb81b7c45c9d873b934f78d055aa4b4', 'image_sha256': '5d4fb071387fba8ddd91d8cbb939706be545d746ecb4c951068bf92744128825'}, '14': {'index': 435003, 'path': '10011101100111', 'projection_raw_sha256': '68a09e4ea489e50f0a87e87c2ddd2f57fe79361c01c518647b03c0f4d1325ea8', 'image_sha256': '45efdbaac9cb0bc52d72cd00b842aedbfb2d7dec096f83ad8e7670d2661edbf8'}}

def require(test, message):
    if not test:
        raise ValueError(message)

def sha_file(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def json_sha(obj):
    raw = json.dumps(obj, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()
    return hashlib.sha256(raw).hexdigest()

def write_json(p, obj):
    p = Path(p); p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_name(p.name + '.tmp')
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n')
    tmp.replace(p)

def parse_image(aux):
    require(isinstance(aux, list) and len(aux) == 24, 'Bad B24 dimension')
    out = {}
    for name, row in zip(ORDER, aux):
        require(isinstance(row, list) and len(row) == 2, 'Bad interval')
        require(all(type(v) in (str, int) for v in row), 'Nonexact interval endpoint')
        lo, hi = map(Q, row)
        require(lo <= hi, 'Reversed interval')
        out[name] = I(lo, hi)
    return out

def prove_canonical_cover(aux):
    """A mathematical lemma, applicable only to a V37 canonical source.
    The default source reconstruction establishes that scope; a bare cached box
    is NOT an independent source certificate.
    """
    x = parse_image(aux)
    require(x['F'].lo >= GAMMA, 'Not the frozen high-value source semantics')
    require(x['p'].lo > 1 and x['e'].lo > 0 and x['e'].hi < 1, 'Prefix endpoint guard')
    require(x['beta'].lo >= 0 and x['beta'].hi <= 1, 'Beta base range')
    require(x['v0'].lo >= 0 and x['v1'].hi <= 0 and x['v2'].hi <= 0, 'Beta monotonic signs')
    qv = [x[f'q{i}'] + x[f'v{i}'] for i in range(3)]
    require(qv[0].hi <= 1, 'Beta=1 upper completion for column 0')
    require(qv[1].lo >= -1 and qv[2].lo >= -1, 'Beta=1 lower completions')
    # Other sides improve when beta rises from the ACTUAL feasible beta to 1.
    # Canonical beta is the maximum of precisely that joint interval.
    require(all(x[f'u{i}'].hi < 0 for i in range(3)), 'Strict negative receiver signs')
    require(x['x0'].lo > 0 and x['x1'].hi < 0 and x['x2'].lo > 0, 'Strict prefix x signs')
    head = 1 - x['p'] + x['e']
    require(head.lo > 0, 'Head row may be active')
    u, v, w = -x['u0'], -x['u1'], -x['u2']
    xx, zz, yy = x['x0'], -x['x1'], x['x2']
    d01 = xx*v + zz*u
    d12 = yy*v + zz*w
    require(d01.lo > 0 and d12.lo > 0, 'Nonpositive shared prefix denominator')
    return {
        'theorem': 'V37_CANONICAL_BETA_ONE_AND_TWO_PREFIX_BASES',
        'beta_forced': '1', 'beta_endpoint_images': [z.data() for z in qv],
        'head_slack_after_beta_one': head.data(),
        'e_interval': x['e'].data(),
        'denominator_intervals': {LABELS[0]: d01.data(), LABELS[1]: d12.data()},
        'complete_labels': list(LABELS),
        'zero_coefficient_cases': 'excluded by strict SOURCE bounds, not epsilon deletion',
        'chart_overlap': 'allowed; closed equalities are retained',
    }


def check_source_bytes(dep,parent_file,projection_file):
    require(str(dep) in SPECS,'Unassigned source')
    require(sha_file(parent_file)==PARENT_SHA,'Wrong parent raw bytes')
    require(sha_file(projection_file)==SPECS[str(dep)]['projection_raw_sha256'],'Wrong projection raw bytes')

def rebuild_sources(bp,dm,deps):
    parent_file=ROOT/'inputs/parent.json';parent=json.loads(parent_file.read_text())
    partial_file=ROOT/'inputs/PARTIAL_DISCOVERY.json'
    require(sha_file(partial_file)==PARTIAL_SHA,'Wrong latest partial source bytes')
    partial=json.loads(partial_file.read_text())['certificate']
    manifest=json.loads((ROOT/'frozen/deep/runtime/DEEP500_MANIFEST.json').read_text())
    index=json.loads((ROOT/'inputs/SOURCE_INDEX.json').read_text())
    require(index['parent_index']==435003 and index['original_task_id']=='435003_bebe09509f4b934c5496' and index['original_task_path']=='10011101','Wrong source index task')
    prefix,stats=bp.prefix_image(parent,cross_check=True)
    cache={};counts={};records=[]
    for dep in deps:
        sp=SPECS[str(dep)];path=sp['path'];proj=ROOT/f'inputs/projection_{dep}.json'
        check_source_bytes(dep,parent_file,proj)
        entries=[e for e in index['entries'] if e['path']==path]
        require(len(entries)==1 and entries[0]['projection_file_sha256']==sp['projection_raw_sha256'] and entries[0]['parent_file_sha256']==PARENT_SHA,'Wrong source index entry')
        cert=json.loads(proj.read_text())
        if cert['rule']==dm.OLD_RULE:
            dm.validate_legacy_binding(parent,cert,manifest['legacy_rule_identity'],bp)
        else:
            binding=bp.binding(parent)
            require(set(cert)==set(binding)|{'profile','tree'} and all(cert[k]==v for k,v in binding.items()),'Wrong source binding')
            dm.counts(cert['tree'])
        require({k:v for k,v in cert.items() if k!='tree'}=={k:v for k,v in partial.items() if k!='tree'},'Partial/projection envelope mismatch')
        node=cert['tree'];orig=partial['tree'];out=copy.deepcopy(prefix);visits=[]
        for depth in range(len(path)+1):
            key=path[:depth]
            require(node['waves']==orig['waves'],'Projected ancestor wave mismatch')
            signature=(json_sha(out),json_sha(node['waves']),cert['profile'])
            if key in cache:
                require(cache[key][0]==signature,'Inconsistent shared ancestor')
                out=copy.deepcopy(cache[key][1])
            else:
                out=bp.db.common_contract(out,profile=cert['profile'])
                for wave in node['waves']:
                    out=bp.db.apply_wave(out,wave,profile=cert['profile'],cross_check=True)
                cache[key]=(signature,copy.deepcopy(out))
                counts[key]=(len(node['waves']),sum(map(len,node['waves'])))
            require(out['status']=='BOUNDED','Unexpected source-empty result')
            term=node['terminal'];ot=orig['terminal']
            visit={'path':key,'depth':depth,'waves':len(node['waves']),'bounds':sum(map(len,node['waves'])),'waves_sha256':json_sha(node['waves']),'image_sha256':json_sha(out['aux_image']),'kind':term['kind']}
            visits.append(visit)
            if depth==len(path):
                require(term=={'kind':'O'} and ot=={'kind':'O'},'Declared current target is not OPEN');break
            require(term['kind']=='S' and ot['kind']=='S' and type(term['axis']) is int and 0<=term['axis']<24 and term['axis']==ot['axis'],'Wrong ancestor split')
            aux=copy.deepcopy(out['aux_image']);axis=term['axis'];lo,hi=map(Q,aux[axis]);mid=(lo+hi)/2
            require(lo<mid<hi,'Degenerate split')
            side=path[depth];visit.update(axis=axis,side=side,exact_midpoint=str(mid))
            aux[axis][1 if side=='0' else 0]=str(mid)
            out={'status':'BOUNDED','aux_image':aux}
            child='left' if side=='0' else 'right';node=term[child];orig=ot[child]
        require(json_sha(out['aux_image'])==sp['image_sha256'],'Wrong rebuilt image')
        record={'index':435003,'path':path,'source_depth':int(dep),'parent_raw_sha256':PARENT_SHA,'projection_raw_sha256':sp['projection_raw_sha256'],'latest_partial_raw_sha256':PARTIAL_SHA,'image_sha256':sp['image_sha256'],'aux_image':out['aux_image'],'parent_binding':bp.binding(parent),'prefix_stats':stats,'visited_ancestors_and_target':visits,'whole_task_covered':False,'whole_parent_covered':False,'anchor_task_id':'435003_bebe09509f4b934c5496','anchor_path':'10011101','suffix':path[8:],'all_pre_cut_axes_waves_and_target_waves_match_latest':True}
        records.append(record)
        print('SOURCE_REBUILT',path,sp['image_sha256'],flush=True)
    return records,{'prefix_replays':1,'prefix_stats':stats,'unique_visited_nodes':len(cache),'unique_inherited_local_waves':sum(x[0] for x in counts.values()),'unique_inherited_local_bounds':sum(x[1] for x in counts.values()),'no_external_sibling_terminal_replay':True}

def check_certificate_schema(cert,dep):
    expected={'rule','semantics','parent_index','path','parent_raw_sha256','projection_raw_sha256','rebuilt_image_sha256','canonical_cover','branches'}
    require(isinstance(cert,dict) and set(cert)==expected,'Invalid B16 envelope')
    sp=SPECS[str(dep)]
    require(cert['rule']==RULE and cert['semantics']==SEMANTICS,'Wrong rule or conclusion semantics')
    require(type(cert['parent_index']) is int and cert['parent_index']==435003,'Wrong original parent index')
    require(cert['path']==sp['path'],'Wrong target path')
    require(cert['parent_raw_sha256']==PARENT_SHA and cert['projection_raw_sha256']==sp['projection_raw_sha256'] and cert['rebuilt_image_sha256']==sp['image_sha256'],'Wrong source binding')
    require(cert['canonical_cover']==COVER,'Unknown complete chart cover')
    require(isinstance(cert['branches'],list) and len(cert['branches'])==2,'Incomplete chart cover')
    require([b.get('label') for b in cert['branches']]==list(LABELS),'Missing/duplicate/wrong chart')
    for br in cert['branches']:
        require(set(br)=={'label','profile','waves','terminal'},'Bad conditional trace schema')
        require(br['profile']=='PIVOT_CYCLE','Wrong row profile')
        require(isinstance(br['waves'],list) and len(br['waves'])<=128,'Bad finite wave list')
        require(isinstance(br['terminal'],dict) and br['terminal'].get('kind')=='C','Expected complete exact C terminal')
def exact_terminal(db, rows, boxes, term):
    sparse = db.inherited.dual_margin(rows, boxes, term)  # strict schema, weights, and residual
    weights = dict(term['weights'])
    coeff = [sum(Q(w)*rows[j][0].get(i,Q(0)) for j,w in weights.items()) for i in range(len(boxes))]
    rhs = sum(Q(w)*rows[j][1] for j,w in weights.items())
    dense = rhs-sum(c*(z.lo if c>=0 else z.hi) for c,z in zip(coeff,boxes))
    require(sparse==dense, 'Sparse/dense terminal mismatch')
    require(sparse<0, 'Nonnegative exact contradiction remainder')
    return sparse, coeff, rhs

def row_names(bp, aux, label):
    from pivot_windows import WINDOW_ROWS, cycle_rows
    ps=bp.db.fs.BASE_POLYS+bp.db.fs.CHARTS[label][0]+WINDOW_ROWS
    pairs=sorted({m for _,p in ps for m in p if len(m)==2})
    names=[n for n,p in ps]+[f'MCC{m}:{i}' for m in pairs for i in range(4)]+[n for n,p in cycle_rows(aux)]
    return names,pairs

def replay_branch(bp, aux, br):
    aux=copy.deepcopy(aux); aux[10]=['1','1']
    out=bp.db.common_contract({'status':'BOUNDED','aux_image':aux},label=br['label'],profile=br['profile'])
    require(out['status']=='BOUNDED','Use matching interval-empty certificate instead')
    images=[]
    for wave in br['waves']:
        out=bp.db.apply_wave(out,wave,label=br['label'],profile=br['profile'],cross_check=True)
        require(out['status']=='BOUNDED','Unexpected early empty domain')
        images.append({'image_sha256':json_sha(out['aux_image']),'aux_image':out['aux_image']})
    rows,boxes=bp.db.rows_and_bounds(out['aux_image'],label=br['label'],profile=br['profile'])
    margin,coeff,rhs=exact_terminal(bp.db,rows,boxes,br['terminal'])
    names,pairs=row_names(bp,out['aux_image'],br['label'])
    require(len(names)==len(rows),'Row naming mismatch')
    terminals=[]
    for i,w in br['terminal']['weights']:
        a,b=rows[i]
        terminals.append({'row':i,'name':names[i],'weight':w,
                          'coefficients':{str(k):str(v) for k,v in a.items()},'rhs':str(b)})
    result={'label':br['label'],'status':'CONDITIONAL_GAMMA_EXCLUDED',
            'waves':len(br['waves']),'coordinate_bounds':sum(map(len,br['waves'])),
            'final_aux_image':out['aux_image'],'final_image_sha256':json_sha(out['aux_image']),
            'terminal_row_count':len(terminals),'terminal_exact_margin':str(margin),
            'margin_divided_by_10_pow_14':str(margin/Q(10**14)),
            'lifted_dimension':len(boxes),'rows':len(rows),
            'shared_products':[list(m) for m in pairs],
            'terminal_rows':terminals,
            'terminal_combination_rhs':str(rhs),'terminal_combination_coefficients':[str(c) for c in coeff],
            'all_intermediate_images':images}
    return result,(rows,boxes)


def negative_controls(bp,rec,cert,contexts):
    dep=rec['source_depth'];passed=[]
    def reject(name,f):
        try:f()
        except (ValueError,TypeError,KeyError,ZeroDivisionError) as e:
            passed.append({'name':name,'rejected':True,'reason':str(e)});return
        raise ValueError('Failed rejection control '+name)
    def change(k,v):
        c=copy.deepcopy(cert);c[k]=v;return c
    reject('wrong_rule_old_B15',lambda:check_certificate_schema(change('rule','B15_CANONICAL_PREFIX_TWO_CHART_GAMMA_V1'),dep))
    reject('wrong_semantics_ALPHA_SAFE',lambda:check_certificate_schema(change('semantics','ALPHA_SAFE'),dep))
    reject('wrong_path_old_S2',lambda:check_certificate_schema(change('path','1001110111'),dep))
    reject('wrong_path_depth19',lambda:check_certificate_schema(change('path','1001110110011011111'),dep))
    reject('other_new_source',lambda:check_certificate_schema(cert,14 if dep==11 else 11))
    reject('bool_parent_index',lambda:check_certificate_schema(change('parent_index',True),dep))
    reject('wrong_rebuilt_image',lambda:check_certificate_schema(change('rebuilt_image_sha256','0'*64),dep))
    reject('wrong_parent_hash',lambda:check_certificate_schema(change('parent_raw_sha256','0'*64),dep))
    reject('missing_closed_chart',lambda:check_certificate_schema(change('branches',cert['branches'][:1]),dep))
    cc=copy.deepcopy(cert);cc['branches'][1]['label']=LABELS[0]
    reject('duplicate_chart',lambda:check_certificate_schema(cc,dep))
    cc=copy.deepcopy(cert);cc['trusted_beta']=1
    reject('unverified_cached_beta',lambda:check_certificate_schema(cc,dep))
    def img(i,bb):
        a=copy.deepcopy(rec['aux_image']);a[i]=bb;return a
    reject('e_one_boundary_requires_extra_chart',lambda:prove_canonical_cover(img(9,['1/2','1'])))
    reject('zero_u1_coefficient_requires_extra_chart',lambda:prove_canonical_cover(img(12,['-1/2','0'])))
    reject('x0_zero_requires_extra_chart',lambda:prove_canonical_cover(img(14,['0','1/2'])))
    reject('beta1_endpoint_not_feasible',lambda:prove_canonical_cover(img(21,['-2','2'])))
    reject('head_row_may_be_active',lambda:prove_canonical_cover(img(8,['3/2','2'])))
    reject('float_input',lambda:prove_canonical_cover(img(10,[0.9,1.0])))
    rows,boxes=contexts[0];terminal=cert['branches'][0]['terminal']
    for name,bad in [('negative_weight',-1),('zero_weight',0),('boolean_weight',True)]:
        t=copy.deepcopy(terminal);t['weights'][0][1]=bad
        reject(name,lambda t=t:exact_terminal(bp.db,rows,boxes,t))
    t=copy.deepcopy(terminal);t['weights'].append(copy.deepcopy(t['weights'][0]))
    reject('duplicate_row',lambda:exact_terminal(bp.db,rows,boxes,t))
    reject('false_C_terminal',lambda:exact_terminal(bp.db,rows,boxes,{'kind':'C','weights':[[0,1]]}))
    if cert['branches'][0]['waves']:
        b=copy.deepcopy(cert['branches'][0]['waves'][0][0]);b['coordinate']=24
        reject('product_column_target',lambda:bp.db.bound_value(rows,boxes,b))
        b=copy.deepcopy(cert['branches'][0]['waves'][0][0]);b['objective_weight']=0
        reject('zero_objective_multiplier',lambda:bp.db.bound_value(rows,boxes,b))
    with tempfile.TemporaryDirectory() as td:
        pp=Path(td)/'parent.json';cp=Path(td)/'projection.json'
        pp.write_bytes((ROOT/'inputs/parent.json').read_bytes()+b' ')
        cp.write_bytes((ROOT/f'inputs/projection_{dep}.json').read_bytes())
        reject('changed_parent_file',lambda:check_source_bytes(dep,pp,cp))
        pp.write_bytes((ROOT/'inputs/parent.json').read_bytes())
        obj=json.loads(cp.read_text());obj['tree']['terminal']['axis']=(obj['tree']['terminal']['axis']+1)%24
        cp.write_text(json.dumps(obj))
        reject('changed_real_ancestor_axis_file',lambda:check_source_bytes(dep,pp,cp))
    return passed

def check_payload():
    manifest=json.loads((ROOT/'PROOF_PAYLOAD_SHA256.json').read_text())
    require(isinstance(manifest,dict) and manifest.get('schema')=='B16_EXACT_PAYLOAD_V1','Bad payload manifest')
    entries=manifest.get('files')
    require(isinstance(entries,dict) and len(entries)>0,'Empty payload manifest')
    actual={}
    for relative in ('verify_all.py','support','frozen','accepted_inputs','inputs','proof'):
        item=ROOT/relative
        paths=[item] if item.is_file() else item.rglob('*')
        for path in paths:
            if path.is_file() and '__pycache__' not in path.parts and path.suffix!='.pyc':
                actual[path.relative_to(ROOT).as_posix()]=sha_file(path)
    require(actual==entries,'Proof payload files or hashes mismatch')
    return {'files_checked':len(entries),'manifest_sha256':sha_file(ROOT/'PROOF_PAYLOAD_SHA256.json')}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source',choices=('11','14','all'),default='all');ap.add_argument('--output',type=Path);args=ap.parse_args()
    payload=check_payload()
    deps=[11,14] if args.source=='all' else [int(args.source)]
    sys.path.insert(0,str(ROOT/'frozen/deep'));import deep_math as dm
    bp=dm.load_protocol(ROOT/'frozen/deep')
    proofs=[]
    for dep in deps:
        cert=json.loads((ROOT/f'proof/COVERAGE_{dep}.json').read_text());check_certificate_schema(cert,dep);proofs.append(cert)
    records,stats=rebuild_sources(bp,dm,deps)
    results=[]
    for rec,cert in zip(records,proofs):
        cover=prove_canonical_cover(rec['aux_image']);branches=[];contexts=[]
        for br in cert['branches']:
            r,ctx=replay_branch(bp,rec['aux_image'],br);branches.append(r);contexts.append(ctx)
            print('EXACT_CHART_CLOSED',rec['path'],br['label'],r['waves'],r['coordinate_bounds'],flush=True)
        neg=negative_controls(bp,rec,cert,contexts)
        result={'source':rec,'cover_lemma':cover,'branches':branches,'status':SEMANTICS,'new_conditional_waves':sum(b['waves'] for b in branches),'new_coordinate_bounds':sum(b['coordinate_bounds'] for b in branches),'new_geometric_splits':0,'negative_controls':neg,'negative_controls_passed':len(neg),'certificate_file_sha256':sha_file(ROOT/f"proof/COVERAGE_{rec['source_depth']}.json")}
        results.append(result)
    output=args.output or ROOT/f'evidence/VERIFICATION_{args.source}.json'
    result={'rule':RULE,'status':SEMANTICS,'payload_integrity':payload,'source_count':len(results),'results':results,'reconstruction':stats,'new_complete_original_tasks':0,'new_complete_original_parents':0,'production_modified':False,'global_root_replayed':False,'old_S2_replayed':False,'depth19_researched':False,'inherited_theory':['V37 canonical beta and maximal p/minimal e','V39 complete prefix classification','frozen U41/PIVOT_CYCLE rows, propagation, exact weighted remainders'],'claim':'Each selected full canonical high source is empty. No claim about arbitrary noncanonical B24 box points or whole anchor/parent.'}
    write_json(output,result)
    print('B16_EXACT_FIXED_SOURCE_PASS',len(results),sha_file(output),flush=True)
if __name__=='__main__':main()
