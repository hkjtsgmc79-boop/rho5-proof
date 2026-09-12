"""The no-dual control reaches the deterministic propagation fixed point.
Its recorded failure to find a C/H is a discovery observation, not feasibility.
"""
import json,os
from concurrent.futures import ProcessPoolExecutor
from source_access import ROOT,SOURCE,fs
from dual_box import common_contract,rows_and_bounds
from source_access import inherited

def one(n):
    sample=json.loads((SOURCE/'REMAINING_SAMPLES64.json').read_text())[n]
    rec=json.loads((ROOT/'evidence/plain_fixed_point_control.json').read_text())[str(n)]
    out=fs.parent_enclosure(sample['box'])
    for _ in range(rec['passes']):
        before=out;out=common_contract(out,profile='BASE')
    assert out['status']=='BOUNDED'
    if rec['status']=='OPEN':
        assert before.get('aux_image')==out.get('aux_image')
        assert rec['terminal']=={'kind':'O'}
    else:
        assert rec['status']=='EMPTY'and rec['terminal']['kind']=='C'
        rows,boxes=rows_and_bounds(out['aux_image'])
        assert inherited.dual_margin(rows,boxes,rec['terminal'])<0
    return dict(sample_ordinal=n,passes=rec['passes'],status=rec['status'])
def run(jobs=4):
    with ProcessPoolExecutor(max_workers=jobs)as ex:records=list(ex.map(one,range(64)))
    return dict(boxes=64,exact_propagation_fixed_points=sum(r['status']=='OPEN'for r in records),
      complete_samples=[r['sample_ordinal']for r in records if r['status']=='EMPTY'],
      maximum_passes_to_fixed_point=max(r['passes']for r in records),
      saved_C_H_discovery_successes=sum(r['status']=='EMPTY'for r in records),
      no_claim_that_other_C_H_proposals_cannot_exist=True)
if __name__=='__main__':print(json.dumps(run(int(os.environ.get('V41_JOBS','4'))),indent=2))
