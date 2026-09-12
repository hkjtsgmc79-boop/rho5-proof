#!/usr/bin/env python3
"""Exact V53 source proof and PARTIAL depth-eight anchor composition.
No optimizer is imported. Actual source boxes and every visited intermediate
bound are reconstructed from immutable parent/ancestor data.
"""
from v53_boot import *
from collections import Counter
import importlib.util

ANCHOR='10011101'
TASK='435003_bebe09509f4b934c5496'
B15_PATH='1001110111'
PENDING=('10011101100111','10011101101')
PARENT_HASH='9d7f10cf242dddc51c6fd5a03fed4adf9f4084bb9c3584e801f4693ce093f780'
PROJECTION_HASH='0fd97e1eedd90905584f10fa8c0dba1ee8ae1e197726af22078c3b7f78309edd'
PARTIAL_HASH='b4515303844ba40537cc083d7c6be71cce9f142d3bcbf9023ce2bbeb674988f7'
INDEX_HASH='bc28ba42601c09f89e32086445a6ba3424e5fe2201d2e66b72844fab66cb67b0'
IMAGE_HASH='9fae881a2f63ae8ff1627aa9e58025a2e0ba9e7ad793158b7112a4669e11f199'
PROOF=Path(os.environ.get('V53_PROOF_DIR',str(ROOT))).resolve()
EXPECTED_MARGIN=Q('-1005495384602754603811064507351680469029685784938386479/544451787073501541541399371890829138329600000000000')


def exact_terminal(aux,term,profile='PIVOT_CYCLE'):
    require(isinstance(term,dict) and term.get('kind') in ('C','H'),'Not an exact C/H terminal')
    rows,boxes=bp.db.rows_and_bounds(aux,profile=profile)
    sparse=bp.source.inherited.dual_margin(rows,boxes,term)
    weights=dict(term['weights'])
    coeff=[sum(Q(w)*rows[j][0].get(i,Q(0))for j,w in weights.items())for i in range(len(boxes))]
    rhs=sum(Q(w)*rows[j][1]for j,w in weights.items())
    if term['kind']=='H':coeff[23]-=term['objective_weight']
    minimum=sum(c*(b.lo if c>=0 else b.hi)for c,b in zip(coeff,boxes))
    dense=rhs-minimum
    if term['kind']=='H':dense-=term['objective_weight']*bp.fs.ALPHA
    require(sparse==dense,'Sparse/dense exact residual mismatch')
    require(sparse<0 if term['kind']=='C' else sparse<=0,'Noncontradictory or unsafe terminal')
    return {'kind':term['kind'],'row_count':len(rows),'lifted_coordinates':len(boxes),
            'positive_weights':len(weights),'exact_residual':str(sparse),
            'dense_residual':str(dense),'terminal_sha256':jsha(term)}


def input_identity():
    require(sha(PARENT)==PARENT_HASH,'Wrong complete parent bytes')
    require(sha(PROJECTION)==PROJECTION_HASH,'Wrong depth19 projection bytes')
    partial_file=INPUT/'latest_sources/PARTIAL_DISCOVERY.json'
    require(sha(partial_file)==PARTIAL_HASH,'Wrong partial source snapshot bytes')
    require(sha(INPUT/'SOURCE_INDEX.json')==INDEX_HASH,'Wrong latest source index')
    par=json.loads(PARENT.read_text());partial=json.loads(partial_file.read_text())
    index=json.loads((INPUT/'SOURCE_INDEX.json').read_text())
    require(index['parent_index']==435003 and index['original_task_id']==TASK and index['original_task_path']==ANCHOR,'Wrong anchor identity')
    require(set(index['remaining_research_paths'])=={PATH,*PENDING},'Missing or substituted research obligations')
    cert=partial['certificate'];expect=bp.binding(par)
    require(set(cert)==set(expect)|{'profile','tree'},'Malformed mixed source envelope')
    require({k:cert[k]for k in expect}==expect,'Wrong mixed source binding')
    require(cert['profile']=='PIVOT_CYCLE','Wrong source row profile')
    require(partial['source']['parent_file_sha256']==PARENT_HASH and partial['source']['task_id']==TASK and partial['source']['target_path']==ANCHOR,'Wrong partial anchor source')
    # The projections must be the exact ancestor/target selections of THIS tree.
    mapping=[]
    for entry in index['entries']:
        path=entry['path']; require(path in {PATH,*PENDING},'Unexpected index entry')
        f=INPUT/entry['projection_file'];require(sha(f)==entry['projection_file_sha256'],'Wrong projection identity')
        projection=json.loads(f.read_text());head={k:v for k,v in cert.items()if k!='tree'}
        require({k:v for k,v in projection.items()if k!='tree'}==head,'Wrong projected source header')
        require(projection['tree']==dm.project(cert['tree'],path),'Projected ancestors/target do not match latest source')
        mapping.append({'path':path,'projection_sha256':sha(f),'ancestor_and_target_structure_equal':True})
    require(len(mapping)==3 and {x['path'] for x in mapping}=={PATH,*PENDING},'Duplicate or omitted projection')
    return par,partial,index,mapping


def check_source_schema(spec):
    fields={'schema','semantics','parent_index','local_path','anchor_task_id','anchor_path',
            'parent_raw_sha256','projection_raw_sha256','source_index_sha256','source_snapshot_sha256',
            'source_image_sha256','profile','frozen_rule','frozen_rule_identity','complete_source_projection',
            'complete_source_projection_sha256','terminal_details','terminal_details_sha256','full_source',
            'claim_scope','new_splits','new_waves','new_bounds','new_condition_graphs','extra_propagation_required'}
    require(isinstance(spec,dict)and set(spec)==fields,'Wrong source certificate schema')
    expected={'schema':'V53_SOURCE_BOUND_FROZEN_C_V1','semantics':'GAMMA_EXCLUDED_CANONICAL_SOURCE',
              'parent_index':435003,'local_path':PATH,'anchor_task_id':TASK,'anchor_path':ANCHOR,
              'parent_raw_sha256':PARENT_HASH,'projection_raw_sha256':PROJECTION_HASH,
              'source_index_sha256':INDEX_HASH,'source_snapshot_sha256':PARTIAL_HASH,
              'source_image_sha256':IMAGE_HASH,'profile':'PIVOT_CYCLE','frozen_rule':bp.RULE,
              'frozen_rule_identity':bp.rule_hash(),'full_source':True,
              'complete_source_projection':'DEPTH19_COMPLETE_SOURCE_PROJECTION.json',
              'terminal_details':'TERMINAL_DETAILS.json','new_splits':0,'new_waves':0,'new_bounds':0,
              'new_condition_graphs':0,'extra_propagation_required':False,
              'claim_scope':'only the complete depth19 canonical high source; neither depth8 anchor nor whole parent'}
    for k,v in expected.items():require(type(spec[k])is type(v)and spec[k]==v,'Wrong source claim '+k)
    for k in ['complete_source_projection_sha256','terminal_details_sha256']:
        require(type(spec[k])is str and len(spec[k])==64 and all(c in '0123456789abcdef'for c in spec[k]),'Bad digest')


def check_details(aux,terminal,details):
    from pivot_windows import WINDOW_ROWS, cycle_rows
    rows,boxes=bp.db.rows_and_bounds(aux,profile='PIVOT_CYCLE')
    ps=bp.db.fs.BASE_POLYS+WINDOW_ROWS;pairs=sorted({m for _,p in ps for m in p if len(m)==2})
    names=[n for n,p in ps]+[f'MCC{m}:{i}'for m in pairs for i in range(4)]+[n for n,p in cycle_rows(aux)]
    require(len(names)==len(rows),'Bad row-name dictionary')
    require(details['source_image_sha256']==jsha(aux)and details['aux_image']==aux,'Details cache not equal rebuilt image')
    require(details['condition_label']is None,'Unexpected conditional row')
    selected=[{'row_index':j,'name':names[j],'weight':w,'coefficients':{str(i):str(a)for i,a in rows[j][0].items()},'rhs':str(rows[j][1])}for j,w in terminal['weights']]
    require(details['selected_rows']==selected,'Recorded row is not the rebuilt physical row')
    require(details['shared_products']==[list(m)for m in pairs],'Shared product dictionary changed')
    require(details['lifted_bounds']==[[str(b.lo),str(b.hi)]for b in boxes],'Wrong product boxes')
    ws=dict(terminal['weights']);cs=[sum(Q(w)*rows[j][0].get(i,Q(0))for j,w in ws.items())for i in range(len(boxes))]
    rhs=sum(Q(w)*rows[j][1]for j,w in ws.items());minimum=sum(c*(b.lo if c>=0 else b.hi)for c,b in zip(cs,boxes))
    require(details['weighted_coefficients']==list(map(str,cs))and details['weighted_rhs']==str(rhs),'Wrong aggregate coefficients')
    require(details['box_linear_minimum']==str(minimum)and details['exact_residual']==str(rhs-minimum),'Wrong exact aggregate residual')
    require(rhs-minimum==EXPECTED_MARGIN<0,'Expected negative margin failed')
    require(Q(aux[23][0])>=Q(4132517,1000000) and Q(4132517,1000000)<bp.fs.ALPHA,'Wrong gamma/alpha semantics')
    return exact_terminal(aux,terminal)


def verify_source(par,partial):
    start=time.monotonic();spec=json.loads((PROOF/'SOURCE_CERTIFICATE.json').read_text());check_source_schema(spec)
    proof_file=PROOF/spec['complete_source_projection'];detail_file=PROOF/spec['terminal_details']
    require(sha(proof_file)==spec['complete_source_projection_sha256'],'Wrong proof bytes')
    require(sha(detail_file)==spec['terminal_details_sha256'],'Wrong details bytes')
    received=json.loads(PROJECTION.read_text());completed=json.loads(proof_file.read_text())
    audit=dm.validate_branch_extension(received,completed,PATH)
    before=at(received['tree'],PATH);after=at(completed['tree'],PATH)
    require(before['terminal']=={'kind':'O'}and after['terminal'].get('kind')=='C','Not a whole target C replacement')
    require(before['waves']==after['waves'],'Unrecorded new target wave')
    require(audit['target_counts']['nodes']==1 and audit['target_counts']['C']==1,'Target is not a single complete C')
    rebuilt=source();require(rebuilt['image_sha256']==IMAGE_HASH,'Rebuilt image mismatch')
    # Explicitly show the discovery call added no propagation contraction.
    extra=bp.db.common_contract({'status':'BOUNDED','aux_image':copy.deepcopy(rebuilt['aux_image'])},profile='PIVOT_CYCLE')
    require(extra['status']=='BOUNDED'and extra['aux_image']==rebuilt['aux_image'],'Discovery extra propagation not redundant')
    detail=check_details(rebuilt['aux_image'],after['terminal'],json.loads(detail_file.read_text()))
    original=bp.verify(par,completed,allow_open=True,cross_check=True)
    require(original['counts']['S']==19 and original['counts']['C']==1 and original['counts']['O']==19 and original['status']=='OPEN','Full projection must preserve external OPENs')
    return {'status':'GAMMA_EXCLUDED_CANONICAL_SOURCE','path':PATH,'complete_source':True,'source_open':0,
            'new_splits':0,'new_waves':0,'new_bounds':0,'conditional_graphs':0,'rule_changed':False,
            'whole_parent_closed':False,'whole_anchor_closed':False,'source':rebuilt,
            'terminal_evidence':detail,'original_full_projection_replay':original,'structural_extension':audit,
            'seconds':time.monotonic()-start},completed


def load_b15():
    path=INPUT/'B_STRUCTURE_15/verify_all.py'
    spec=importlib.util.spec_from_file_location('v53_frozen_b15_verifier',path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    return mod


def verify_pending_accounting(ledger):
    require(ledger.get('schema')=='V53_DEPTH8_ANCHOR_COVERAGE_V1','Wrong coverage schema')
    require(ledger.get('anchor_path')==ANCHOR and ledger.get('parent_index')==435003,'Wrong ledger anchor')
    require(ledger.get('status')=='PARTIAL_ALPHA_COVERAGE_TWO_B16_SOURCES_OPEN','Cannot relabel partial anchor as complete')
    pending=[v['path'] for v in ledger['leaves'] if v['classification']=='OPEN_B16']
    require(sorted(pending)==sorted(PENDING)and len(pending)==2,'Missing pending B16 source')
    require(ledger['anchor_closed']is False and ledger['whole_parent_closed']is False and ledger['whole_B_closed']is False,'Unsupported complete claim')
    require(ledger['remaining_sources']==list(PENDING),'Pending identity changed')
    require(ledger['macro_ledger']=='14/15','Unsupported ledger increment')


def verify_anchor(par,partial,index,completed,source_result):
    start=time.monotonic();tree=partial['certificate']['tree'];profile=partial['certificate']['profile']
    b15=load_b15();b15_proof=json.loads((INPUT/'B_STRUCTURE_15/proof/COVERAGE_CERTIFICATE.json').read_text())
    b15.check_certificate_schema(b15_proof)
    b15_projection=json.loads((INPUT/'B_STRUCTURE_15/inputs/projection.json').read_text())
    require(sha(INPUT/'B_STRUCTURE_15/inputs/parent.json')==PARENT_HASH,'B15 wrong original parent')
    require(sha(INPUT/'B_STRUCTURE_15/inputs/projection.json')==b15.PROJECTION_SHA,'B15 wrong projection bytes')
    require(b15_projection['tree']==dm.project(tree,B15_PATH),'B15 source ancestors/target not current source')
    require({k:v for k,v in b15_projection.items()if k!='tree'}=={k:v for k,v in partial['certificate'].items()if k!='tree'},'B15 header not current')
    out,prefix=bp.prefix_image(par,cross_check=True)
    counts=Counter();leaves=[];visited=[];external=[];b15result=None;alpha_detail=[]
    new_term=at(completed['tree'],PATH)['terminal']
    def walk(inbox,node,path):
        nonlocal b15result
        require(isinstance(node,dict) and set(node)=={'waves','terminal'},'Bad node schema')
        if not(ANCHOR.startswith(path)or path.startswith(ANCHOR)):
            require(node=={'waves':[],'terminal':{'kind':'O'}},'Unverified exterior sibling changed')
            external.append({'path':path,'status':'OUTSIDE_ANCHOR_NOT_VERIFIED'});return
        waves=node['waves'];require(type(waves)is list and len(waves)<=128,'Invalid inherited wave list')
        o=bp.db.common_contract(inbox,profile=profile)
        for w in waves:o=bp.db.apply_wave(o,w,profile=profile,cross_check=True)
        t=node['terminal'];require(type(t)is dict,'Bad terminal');kind=t.get('kind')
        ih=jsha(o['aux_image'])if o['status']=='BOUNDED'else None
        event={'path':path,'waves':len(waves),'bounds':sum(map(len,waves)),'waves_sha256':jsha(waves),'kind':kind,'image_sha256':ih}
        visited.append(event)
        inside=path.startswith(ANCHOR)
        if inside:
            counts['nodes']+=1;counts['waves']+=len(waves);counts['bounds']+=sum(map(len,waves))
        if kind=='S':
            require(set(t)=={'kind','axis','left','right'},'Incomplete split')
            require(o['status']=='BOUNDED','Split of empty source')
            ax=t['axis'];require(type(ax)is int and 0<=ax<24,'Invalid split axis')
            lo,hi=map(Q,o['aux_image'][ax]);mid=(lo+hi)/2;require(lo<mid<hi,'Degenerate split')
            event.update(axis=ax,midpoint=str(mid))
            if inside:counts['splits']+=1
            for side in ('0','1'):
                aux=copy.deepcopy(o['aux_image']);aux[ax][1 if side=='0'else 0]=str(mid)
                walk({'status':'BOUNDED','aux_image':aux},t['left'if side=='0'else'right'],path+side)
            return
        require(inside,'Premature terminal before anchor')
        rec={'path':path,'depth':len(path),'local_depth_from_anchor':len(path)-len(ANCHOR),'source_image_sha256':ih,
             'original_kind':kind,'original_terminal_sha256':jsha(t),'target_waves_sha256':jsha(waves)}
        if kind=='I':
            require(t=={'kind':'I'}and o['status']=='EMPTY','False interval leaf');rec['classification']='OLD_GAMMA_EXCLUSION_I'
        elif kind in ('C','H'):
            require(o['status']=='BOUNDED','Unexpected propagated empty source, original terminal mismatch')
            rec['evidence']=exact_terminal(o['aux_image'],t,profile)
            rec['classification']='OLD_GAMMA_EXCLUSION_C'if kind=='C'else'OLD_ALPHA_SAFE_H'
        elif kind=='A':
            require(t=={'kind':'A'}and o['status']=='BOUNDED','Bad alpha leaf')
            port=bp.fs.safe_port(o['aux_image']);require(port is not None,'False original alpha leaf')
            rec['classification']='OLD_ALPHA_SAFE_A';rec['evidence']=port
        elif kind=='N':
            require(set(t)=={'kind','port'}and o['status']=='BOUNDED','Bad source-bound alpha port')
            detail=ac.verify_port(o['aux_image'],t['port'],centers)
            require(detail['status']=='ALPHA_SAFE','False alpha port')
            rec['classification']='B14_ALPHA_SAFE';rec['evidence']=detail;alpha_detail.append((o['aux_image'],t['port']))
        elif kind=='O':
            require(t=={'kind':'O'}and o['status']=='BOUNDED','Bad pending source')
            if path==PATH:
                require(ih==source_result['source']['image_sha256'],'New C sources differ')
                require(waves==at(completed['tree'],path)['waves'],'New source target waves differ')
                rec['classification']='NEW_V53_GAMMA_EXCLUSION_C';rec['evidence']=exact_terminal(o['aux_image'],new_term,profile)
            elif path==B15_PATH:
                require(ih==b15.IMAGE_SHA==b15_proof['rebuilt_image_sha256'],'B15 source image does not match current source')
                guards=b15.prove_canonical_cover(o['aux_image']);branches=[]
                for br in b15_proof['branches']:
                    verified,_=b15.replay_branch(bp,o['aux_image'],br);branches.append(verified)
                b15result={'status':b15.SEMANTICS,'path':path,'old_projection_sha256':b15.PROJECTION_SHA,'current_source_image_sha256':ih,
                           'common_ancestors_and_target_verified':True,'cover_lemma':guards,'branches':branches,
                           'inherited_conditional_waves':sum(z['waves']for z in branches),'inherited_conditional_bounds':sum(z['coordinate_bounds']for z in branches),
                           'proof_sha256':sha(INPUT/'B_STRUCTURE_15/proof/COVERAGE_CERTIFICATE.json')}
                rec['classification']='B15_GAMMA_EXCLUDED_CANONICAL_SOURCE'
                rec['evidence']={'rule':b15.RULE,'proof_sha256':b15result['proof_sha256'],'complete_charts':len(branches),
                                 'exact_margins':[z['terminal_exact_margin']for z in branches]}
            else:
                require(path in PENDING,'Unaccounted OPEN in current anchor')
                record=next(z for z in index['entries']if z['path']==path)
                rec['classification']='OPEN_B16';rec['evidence']={'assigned_to':'B16','projection_sha256':record['projection_file_sha256'],
                                  'expected_semantics':['ALPHA_SAFE','GAMMA_EXCLUDED_CANONICAL_SOURCE'],
                                  'requires_actual_mathematical_replay':True,'receipt_alone_is_not_evidence':True}
        else:raise ValueError('Unknown mixed terminal '+str(kind))
        leaves.append(rec);counts[rec['classification']]+=1
    walk(out,tree,'')
    require(counts['nodes']==2*counts['splits']+1 and len(leaves)==counts['splits']+1,'Incomplete anchor binary cover')
    require(b15result is not None,'B15 not visited')
    require(sum(v['classification']=='NEW_V53_GAMMA_EXCLUSION_C'for v in leaves)==1,'Missing/new source duplication')
    outside_prefix=sorted(external,key=lambda x:x['path'])
    ledger={'schema':'V53_DEPTH8_ANCHOR_COVERAGE_V1','status':'PARTIAL_ALPHA_COVERAGE_TWO_B16_SOURCES_OPEN',
            'parent_index':435003,'parent_sha256':PARENT_HASH,'task_id':TASK,'anchor_path':ANCHOR,
            'source_partial_sha256':PARTIAL_HASH,'source_index_sha256':INDEX_HASH,
            'counts':dict(counts),'leaves':leaves,'visited_nodes':visited,'outside_anchor':outside_prefix,
            'remaining_sources':list(PENDING),'anchor_closed':False,'whole_parent_closed':False,'whole_B_closed':False,
            'macro_ledger':'14/15','old_snapshot_mathematical_acceptance_not_trusted':True,
            'new_splits':0,'new_waves':0,'new_coordinate_bounds':0,
            'received_global_root_replayed':False,'production_modified':False,
            'prefix_stats':prefix,'seconds':time.monotonic()-start}
    verify_pending_accounting(ledger)
    return ledger,b15result,alpha_detail


def derive_maximal_cuts(ledger):
    """Merge only fully paid siblings from the freshly verified anchor tree."""
    verify_pending_accounting(ledger)
    leaf={x['path']:x for x in ledger['leaves']}
    nodes={x['path']:x for x in ledger['visited_nodes']}
    cache={}
    def classify(path):
        if path in leaf:
            row=leaf[path]
            if row['classification']=='OPEN_B16':answer=(False,False,[row])
            else:answer=(True,'ALPHA_SAFE' in row['classification'],[row])
        else:
            require(path in nodes and nodes[path]['kind']=='S','Missing binary coverage node')
            l=classify(path+'0');r=classify(path+'1')
            answer=(l[0] and r[0],l[1] or r[1],l[2]+r[2])
        cache[path]=answer;return answer
    require(not classify(ANCHOR)[0],'Anchor must still be partial')
    cuts=[];pending=[]
    def walk(path):
        paid,has_alpha,records=cache[path]
        if paid:
            cuts.append({'path':path,'depth':len(path),
                         'semantics':'ALPHA_SAFE' if has_alpha else 'GAMMA_EXCLUDED_CANONICAL_SOURCE',
                         'complete_source':True,'supporting_anchor_leaves':len(records),
                         'supporting_paths':[x['path']for x in records],
                         'supporting_leaf_records_sha256':jsha(records),
                         'depends_on_new_depth19':any(x['classification']=='NEW_V53_GAMMA_EXCLUSION_C'for x in records),
                         'source_image_sha256':nodes[path]['image_sha256'],
                         'source_node_waves_sha256':nodes[path]['waves_sha256']})
        elif path in leaf:pending.append(path)
        else:walk(path+'0');walk(path+'1')
    walk(ANCHOR)
    require(set(pending)==set(PENDING),'Reduced coverage lost a pending source')
    new=[x for x in cuts if x['depends_on_new_depth19']]
    require(len(new)==1 and new[0]['path']=='10011101100110' and new[0]['semantics']=='ALPHA_SAFE','Wrong new composite alpha ancestor')
    require(new[0]['supporting_anchor_leaves']==22,'Wrong composite ancestor support')
    require(len(cuts)==5 and len(pending)==2,'Wrong reduced antichain')
    return {'schema':'V53_MAXIMAL_SOURCE_CUTS_V1','anchor_path':ANCHOR,'parent_index':435003,
            'original_partial_sha256':PARTIAL_HASH,'parent_raw_sha256':PARENT_HASH,
            'safe_antichain':cuts,'open_antichain':pending,
            'newly_completed_composite_alpha_source':new[0],
            'new_source_and_composite_ancestor_are_not_two_disjoint_credits':True,
            'complete_original_task':False,'macro_ledger':'14/15'}


def negative_controls(par,partial,source_result,completed,ledger,alpha_examples):
    passed=[]
    def reject(name,fn,layer):
        try:fn()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError)as exc:
            passed.append({'name':name,'rejected':True,'layer':layer,'reason':str(exc)});return
        raise ValueError('Invalid input not rejected: '+name)
    spec=json.loads((PROOF/'SOURCE_CERTIFICATE.json').read_text())
    for field,value in [('parent_index',True),('parent_index',338726),('local_path',PATH[:-1]+'0'),('local_path',ANCHOR),
                        ('projection_raw_sha256','0'*64),('source_image_sha256','0'*64),
                        ('semantics','WHOLE_B_CLOSED'),('new_condition_graphs',1),('extra_propagation_required',True)]:
        x=copy.deepcopy(spec);x[field]=value
        reject('source_'+field+'_'+str(value),lambda x=x:check_source_schema(x),'scope/schema')
    received=json.loads(PROJECTION.read_text())
    x=copy.deepcopy(completed);x['tree']['terminal']['axis']=(x['tree']['terminal']['axis']+1)%24
    reject('changed_ancestor_axis',lambda:dm.validate_branch_extension(received,x,PATH),'exact structure')
    y=copy.deepcopy(completed);y['tree']['terminal']['left']={'waves':[],'terminal':{'kind':'I'}}
    reject('false_exterior_sibling_closed',lambda:dm.validate_branch_extension(received,y,PATH),'exact structure')
    aux=source_result['source']['aux_image'];terminal=at(completed['tree'],PATH)['terminal']
    for name,value in [('negative',-1),('zero',0),('boolean',True)]:
        t=copy.deepcopy(terminal);t['weights'][0][1]=value
        reject(name+'_weight',lambda t=t:exact_terminal(aux,t),'rational terminal')
    t=copy.deepcopy(terminal);t['weights'].append(copy.deepcopy(t['weights'][0]))
    reject('duplicate_row',lambda:exact_terminal(aux,t),'rational terminal')
    t=copy.deepcopy(terminal);t['weights'][0][0]=692
    reject('out_of_range_row',lambda:exact_terminal(aux,t),'rational terminal')
    reject('false_C_no_negative_remainder',lambda:exact_terminal(aux,{'kind':'C','weights':[[0,1]]}),'rational terminal')
    reject('OPEN_disguised_as_proof',lambda:exact_terminal(aux,{'kind':'O'}),'rational terminal')
    if alpha_examples:
        a,p=alpha_examples[0];bad=copy.deepcopy(p);bad['branches']=bad['branches'][:1]
        reject('missing_closed_sorting_branch',lambda:ac.verify_port(a,bad,centers),'full alpha port')
        bad=copy.deepcopy(p);bad['semantic']='GAMMA_EXCLUDED_CANONICAL_SOURCE'
        reject('alpha_relabelled_gamma',lambda:ac.verify_port(a,bad,centers),'full alpha port')
    ll=copy.deepcopy(ledger);ll['leaves']=[x for x in ll['leaves']if x['path']!=PENDING[0]]
    reject('omitted_pending_depth14',lambda:verify_pending_accounting(ll),'coverage accounting')
    ll=copy.deepcopy(ledger);ll['status']='WHOLE_ANCHOR_CLOSED';ll['anchor_closed']=True
    reject('premature_anchor_closure',lambda:verify_pending_accounting(ll),'coverage accounting')
    return {'count':len(passed),'controls':passed,'does_not_claim_second_independent_formal_system':True}


def main():
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=ROOT/'V53_REPLAY_RESULT.json');parser.add_argument('--artifacts',type=Path,default=ROOT/'verified');parser.add_argument('--require-anchor-complete',action='store_true');parser.add_argument('--source-only',action='store_true');args=parser.parse_args()
    start=time.monotonic();par,partial,index,mapping=input_identity()
    print('LATEST_INPUT_AND_THREE_SOURCE_MAPPING_PASS',flush=True)
    sr,completed=verify_source(par,partial)
    print('DEPTH19_ENTIRE_SOURCE_GAMMA_EXCLUDED',sr['terminal_evidence']['exact_residual'],flush=True)
    save(args.artifacts/'DEPTH19_SOURCE_REPLAY.json',sr)
    if args.source_only:
        require(not args.require_anchor_complete,'Source-only cannot prove anchor closure')
        result={'status':'V53_DEPTH19_ENTIRE_SOURCE_EXACT_PASS','semantics':'GAMMA_EXCLUDED_CANONICAL_SOURCE','parent_index':435003,'path':PATH,'source_complete':True,'source_open':0,'parent_closed':False,'anchor_closed':False,'macro_ledger':'14/15','exact_residual':sr['terminal_evidence']['exact_residual'],'new_splits':0,'new_waves':0,'original_full_projection_replay':sr['original_full_projection_replay'],'seconds':time.monotonic()-start}
        save(args.output,result);print(json.dumps(result,ensure_ascii=False,separators=(',',':')),flush=True);return
    ledger,b15detail,alpha_examples=verify_anchor(par,partial,index,completed,sr)
    print('ANCHOR_LEAF_BY_LEAF_REPLAY',json.dumps(ledger['counts'],ensure_ascii=False),flush=True)
    cuts=derive_maximal_cuts(ledger)
    save(args.artifacts/'V53_MAXIMAL_CUTS.json',cuts)
    print('NEW_COMPOSITE_ALPHA_ANCESTOR',cuts['newly_completed_composite_alpha_source']['path'],flush=True)
    neg=negative_controls(par,partial,sr,completed,ledger,alpha_examples)
    print('NEGATIVE_CONTROLS',neg['count'],flush=True)
    save(args.artifacts/'V53_ANCHOR_COVERAGE.json',ledger);save(args.artifacts/'B15_CURRENT_SOURCE_REPLAY.json',b15detail)
    save(args.artifacts/'NEGATIVE_CONTROLS.json',neg)
    result={'status':'V53_DEPTH19_COMPLETE_AND_ANCHOR_TWO_OPEN_EXACT_PASS',
            'new_complete_source_paths':[PATH],'new_complete_original_parents':[],
            'canonical_high_source_semantics':'GAMMA_EXCLUDED_CANONICAL_SOURCE',
            'new_source_terminal':'C','new_splits':0,'new_waves':0,'new_bounds':0,'new_condition_graphs':0,
            'source_original_projection':sr['original_full_projection_replay'],
            'new_C_margin':sr['terminal_evidence']['exact_residual'],
            'source_rebuilt_image_sha256':sr['source']['image_sha256'],
            'anchor_counts':ledger['counts'],'anchor_remaining_sources':ledger['remaining_sources'],
            'anchor_closed':False,'whole_parent_closed':False,'whole_B_closed':False,
            'new_composite_alpha_ancestor':cuts['newly_completed_composite_alpha_source'],
            'maximal_safe_source_count':len(cuts['safe_antichain']),
            'inherited_B15_verified_current_source':True,'inherited_B15_conditional_waves':b15detail['inherited_conditional_waves'],
            'inherited_B15_conditional_bounds':b15detail['inherited_conditional_bounds'],
            'latest_source_index_and_projections_rebuilt':mapping,'negative_controls':neg,
            'unreceived_global_root_replayed_here':False,'production_modified':False,'macro_ledger':'14/15',
            'frozen_mathematical_rule_changed':False,'new_composition_wrapper':'V53_DEPTH8_ANCHOR_COVERAGE_V1',
            'seconds':time.monotonic()-start}
    save(args.output,result)
    print(json.dumps(result,ensure_ascii=False,separators=(',',':')),flush=True)
    if args.require_anchor_complete:
        raise ValueError('Anchor is not complete: two B16 obligations still OPEN; partial exact accounting only')

if __name__=='__main__':main()
