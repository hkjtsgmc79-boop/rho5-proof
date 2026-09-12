"""Replay the saved matched-budget experiment; no optimization is rerun.
OPEN means only that the saved bounded attempt did not produce a terminal.
"""
from pathlib import Path
import gzip,json
from concurrent.futures import ProcessPoolExecutor
from source_access import ROOT,SOURCE
from dual_box import replay_trace

def worker(job):
    profile,n,box,trace=job
    result=replay_trace(box,trace,allow_open=True)
    return dict(profile=profile,sample_ordinal=n,**result)

def run(jobs=4):
    samples=json.loads((SOURCE/'REMAINING_SAMPLES64.json').read_text())
    with gzip.open(ROOT/'evidence/three_wave_ablation.json.gz','rt')as f:data=json.load(f)
    jobspec=[]
    for profile,records in data.items():
        assert set(records)=={str(n)for n in range(64)}
        for n,trace in records.items():
            assert trace['profile']==profile and len(trace['waves'])<=3
            jobspec.append((profile,int(n),samples[int(n)]['box'],trace))
    with ProcessPoolExecutor(max_workers=jobs)as pool:out=list(pool.map(worker,jobspec))
    summary={}
    for p in data:
        row=[x for x in out if x['profile']==p]
        summary[p]=dict(complete=sum(x['status']!='OPEN'for x in row),open_samples=sorted(x['sample_ordinal']for x in row if x['status']=='OPEN'),bounds=sum(x['bounds']for x in row))
    # Extra bounded BASE attempts. They are only diagnostics, not claims that
    # arbitrary future BASE search is incapable of solving a box.
    with gzip.open(ROOT/'evidence/extended_BASE_diagnostics.json.gz','rt')as f:extra=json.load(f)
    extended=[]
    for n,tr in extra.items():
        result=replay_trace(samples[int(n)]['box'],tr,allow_open=True)
        result.pop('aux_image',None);extended.append(dict(sample_ordinal=int(n),**result))
    return dict(matched_maximum_waves=3,maximum_retained_bounds_per_wave=16,
       profiles=summary,extended_BASE_diagnostics=extended,
       interpretation='finite discovery comparison, not a completeness or speed theorem')
if __name__=='__main__':
    import os
    print(json.dumps(run(int(os.environ.get('V41_JOBS','4'))),indent=2))
