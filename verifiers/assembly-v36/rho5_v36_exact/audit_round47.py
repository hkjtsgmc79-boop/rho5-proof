"""Review received LIGHT archive: never replays absent full roots."""
from pathlib import Path
import hashlib,json,sys,time
R=Path(__file__).parent;D=R/'inputs/round47';S=D/'source'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 start=time.monotonic();manifest=json.loads((D/'LIGHT_MANIFEST.json').read_text())
 for n,h in manifest['files'].items():
  assert (D/n).is_file(),n
  assert sha(D/n)==h,n
 sys.path.insert(0,str(S))
 from build_models import make_model,headers
 from verify_local_certificate import verify
 models={}
 for n in ('I_LOW_ALPHA','II_LOW_ALPHA'):
  p=S/'models'/n/'model.json';a=json.loads(p.read_text());b=make_model(a['K'],a['J'],a['type'],a['branch'])
  assert a==b,n
  old=json.loads((S/'reference/parent_models'/f'{n}.json').read_text())
  # Verify actual rows, intervals and products, not only metadata.
  keys=('variables','pairs','rows','root_numerators','root_denominator','K','J','type','branch','target')
  comparisons={}
  for k in keys:
   assert (k in old)==(k in a),k
   if k in a: assert a[k]==old[k],(n,k); comparisons[k]=True
  rec=manifest['models'][n];assert rec['model_sha256']==sha(p)
  assert rec['parent_model_sha256']==sha(S/'reference/parent_models'/f'{n}.json')
  for file in ('evidence/STRICT_REPLAY_RESULT.json','evidence/PORTABLE_COLD_REPLAY_RESULT.json'):
   rr=json.loads((D/file).read_text())['models'][n]
   for k in ('nodes','splits','leaves','contradiction_leaves','alpha_safe_leaves','weighted_height_leaves','open','max_depth','model_sha256'):
    assert rr[k]==rec[k],(n,k)
  assert rec['open']==0
  assert rec['nodes']==2*rec['splits']+1
  assert rec['leaves']==rec['splits']+1
  assert rec['leaves']==rec['contradiction_leaves']+rec['alpha_safe_leaves']
  models[n]={'model_sha256':sha(p),'semantic_equal_to_rebuild':True,'unchanged_original_fields':comparisons,'received_local_receipt':rec,'absent_full_tree_replayed_here':False}
 assert sha(S/'alpha.json')=='9af09b9d6e584bba2a7cef7e9e3993f128fbc90744335eb0c22c8b11e0226959'
 assert sha(S/'local_wall_certificate.json')=='5d43a6936c0fe574d13ebc5c90ecd5762990bf64f2a358cfe4106eb210f8f132'
 assert sha(S/'source/factor_graph.hpp')=='157c63d6d6b3c170241e36e7a28c4ab722cfc6bb97a41b791e99ec7ebced9379'
 assert sha(S/'WEIGHTED_HEIGHT_RULE.json')=='8604d6e7226badfd36ee749a96c6b944dcd4846d89e6726b0498624e3c9b2eb8'
 local=verify(json.loads((S/'local_wall_certificate.json').read_text()))
 out={'status':'V36_ROUND47_LIGHT_INTERFACE_REVIEW_PASS','received_files_hashed':len(manifest['files']),'models':models,'original_local_certificate_reverified':local,'missing_large_trees_replayed_here':False,'totals':{k:sum(m['received_local_receipt'][k] for m in models.values()) for k in ('nodes','splits','leaves','contradiction_leaves','alpha_safe_leaves','weighted_height_leaves','open')},'seconds':time.monotonic()-start}
 (R/'evidence/round47_review.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items() if k not in ('models','original_local_certificate_reverified')},indent=2))
if __name__=='__main__':main()
