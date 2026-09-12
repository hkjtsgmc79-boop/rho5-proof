"""Replay each received-box certificate, including every intermediate bound."""
import json,time,gzip
from concurrent.futures import ProcessPoolExecutor
from source_access import ROOT,SOURCE
from v41_protocol import verify
from dual_box import replay_trace

def one(n):
    i=json.loads((ROOT/'INSERTION_INDEX.json').read_text())[n]
    cert=json.loads((ROOT/i['certificate']).read_text());start=time.time()
    out=verify(i['box'],cert,allow_open=True,cross_check=True)
    return dict(sample_ordinal=n,reported_original_index=i['reported_original_index'],profile=cert['trace']['profile'],**out,seconds=time.time()-start)

def run(jobs=4):
    with ProcessPoolExecutor(max_workers=jobs)as ex:items=list(ex.map(one,range(64)))
    return dict(cases=items,complete_parent_boxes=sum(x['status']!='OPEN'for x in items),
       contradiction_parents=sum(x['status']=='EMPTY'for x in items),alpha_safe_parents=sum(x['status']=='SAFE'for x in items),
       remaining_sample_boxes=[x['sample_ordinal']for x in items if x['status']=='OPEN'],
       all_intermediate_bounds_replayed=sum(x['bounds']for x in items),
       dense_residual_crosschecks=sum(x['bounds']for x in items),
       total_waves=sum(x['waves']for x in items),
       BASE_complete=sum(x['status']!='OPEN'and x['profile']=='BASE'for x in items),
       PIVOT_CYCLE_complete=sum(x['status']!='OPEN'and x['profile']=='PIVOT_CYCLE'for x in items))
if __name__=='__main__':
    import os
    print(json.dumps(run(int(os.environ.get('V41_JOBS','4'))),indent=2))
