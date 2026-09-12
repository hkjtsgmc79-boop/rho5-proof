"""Exact re-certification of V42 one-slack gains on unchanged B02 outer cubes."""
from fractions import Fraction as Q
from pathlib import Path
import json,sys
from _v42_bootstrap import prepare,b02_api,canonical_hash
from transport_box import ONE_SLACK_COSTS,RHO

def check(data=None):
    b=b02_api();p=prepare()['b02']
    if data is None:data=json.loads((p/'accepted_inputs/local_wall_certificate.json').read_text())
    old=b.certify_local(data);rows=[]
    for c,K in zip(old['cases'],ONE_SLACK_COSTS):
        dirs=c['directions'];plus=next(x for x in dirs if x['label']=='O12+')
        minus=next(x for x in dirs if x['label']=='O22-')
        gain=plus['conservative_gain'];speed=plus['exact_speed_bound']
        if not speed<K*gain:raise ValueError('Invalid new travel coefficient')
        if not Q(1,625)<gain:raise ValueError('Insufficient initial slack budget')
        if not minus['full_cube_slack_upper']<Q(3,500)<Q(1,2):raise ValueError('Opposite slack cap')
        if not K<Q(200,3):raise ValueError('Not an improvement')
        rows.append(dict(case=c['case'],cost=str(K),gain=str(gain),speed=str(speed),
             speed_over_gain=str(speed/gain),opposite_slack_upper=str(minus['full_cube_slack_upper']),
             inactive_lower=str(c['minimum_inactive']),qnorm=str(c['qnorm'])))
    return dict(status='V42_ONE_SLACK_FOUR_CUBES_EXACT_PASS',radius=str(RHO),directions=rows,
                dependence='unchanged B02 physical chart, full X alpha theorem',old_radius_expanded=False)

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--output');a=ap.parse_args();r=check()
    s=json.dumps(r,indent=2)
    if a.output:Path(a.output).write_text(s+'\n')
    print(json.dumps(r))
