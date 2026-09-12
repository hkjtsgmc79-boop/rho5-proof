"""Independently verify stored cycle witnesses from actual checkpoint source boxes."""
from pathlib import Path
from fractions import Fraction as Q
import sys,json,hashlib
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from physical_packets import build_packets
from factor_feasibility import Interval,verify
UNIT=(10**9)<<128
records=json.loads((ROOT/'evidence/physical_factor_certificates.json').read_text())
cycles=0;masks=0
for rec in records:
 model=ROOT/'models'/rec['model']/'model.json'
 assert hashlib.sha256(model.read_bytes()).hexdigest()==rec['model_sha256']
 data=json.loads(model.read_text());lo,hi=[[x<<128 for x in row] for row in data['root_numerators']]
 for j,side in rec['path']:
  assert type(j)==int and 0<=j<23 and side in (0,1)
  assert (lo[j]+hi[j])%2==0;m=(lo[j]+hi[j])//2
  assert lo[j]<m<hi[j]
  if side:lo[j]=m
  else:hi[j]=m
 assert list(map(str,lo))==rec['lo'] and list(map(str,hi))==rec['hi']
 packets,err=build_packets([(Q(l,UNIT),Q(h,UNIT))for l,h in zip(lo,hi)],data['type']);assert err is None
 p=packets[rec['layer']];cert=rec['certificate'];assert cert['status']=='UNSAT'
 verify([Interval(*x)for x in p['left']],[Interval(*x)for x in p['right']],
        [[Interval(*x)for x in row]for row in p['cells']],cert)
 masks+=len(cert['branches']);cycles+=sum(x['kind']=='negative_cycle'for x in cert['branches'])
assert cycles>0
print(json.dumps({'status':'ACTUAL_SOURCE_BOX_CYCLE_CERTIFICATES_PASS','boxes':len(records),
 'sign_masks_checked':masks,'strict_cycle_certificates':cycles,'full_domain_claim':False}))
