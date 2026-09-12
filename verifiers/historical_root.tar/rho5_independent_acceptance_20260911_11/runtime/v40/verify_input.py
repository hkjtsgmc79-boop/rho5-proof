from pathlib import Path
import hashlib,json
import bootstrap

def run():
 root=bootstrap.RECEIVED;counts={}
 for name,key in [('R49_SOURCE_MANIFEST.json','files'),('v39/MANIFEST.json','sha256')]:
  p=root/name;data=json.loads(p.read_text())[key]
  for rel,expected in data.items():
   f=p.parent/rel
   if not f.is_file()or hashlib.sha256(f.read_bytes()).hexdigest()!=expected:raise ValueError('Received source mismatch: '+str(rel))
  counts[name]=len(data)
 records=[json.loads((root/'receipts'/n).read_text())for n in ('FROZEN_ROOT_REPLAY.json','COLD_REPLAY.json')]
 for r in records:
  assert r['nodes']==749693 and r['splits']==374846 and r['contradictions']==360642 and r['open']==14205
  assert r['tree_sha256']=='724b10b0eabf3cdee676d6bcbff99d72269b6a6fb1fdddca7446a05badd03701'
  assert r['model_sha256']=='39a65f2cbd6089dab3a403c6a72f365a02003737a641be86c3cf73cb70e76de3'
 from protocol import validate_box,box_hash,MODEL_SHA
 samples=json.loads((bootstrap.ROOT/'inputs/REMAINING_SAMPLES64.json').read_text())
 assert samples==json.loads((root/'REMAINING_SAMPLES64.json').read_text())
 assert len(samples)==64 and len({x['index']for x in samples})==64
 for row in samples:assert box_hash(validate_box(row['box']))==row['box_sha256']and row['status']=='OPEN'
 report=(bootstrap.ROOT/'inputs/ROUND49_REPORT.md').read_bytes()
 assert report==(root/'ROUND49_REPORT.md').read_bytes()
 return {'received_source_manifest_files':counts,'manifests_overlap_not_additive':True,
         'checked_exact_sample_boxes':64,'local_receipts_agree':True,'unreceived_round49_tree_replayed_here':False,
         'actual_parent_split_axes_not_received':True,'source_archive_sha256':bootstrap.ARCHIVE_SHA,
         'model_sha256':MODEL_SHA,'macro_ledger':'14/15'}
if __name__=='__main__':print(json.dumps(run(),indent=2))
