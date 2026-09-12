#!/usr/bin/env python3
from pathlib import Path
import tempfile,json,sys,subprocess
from unittest.mock import patch
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'discovery'))
import frontier_parallel as fp

def verify():
 with tempfile.TemporaryDirectory(prefix='v35_protocol_') as t:
  r=Path(t);m=r/'models/M';m.mkdir(parents=True);(m/'model.json').write_text('{}');d=r/'job';d.mkdir();(d/'checkpoint.tree').write_text('O\n');(d/'next.tree').write_text('UNACCEPTED\n');(d/'STATUS.json').write_text('{"previous":"accepted"}')
  old=(d/'checkpoint.tree').read_bytes();old_status=(d/'STATUS.json').read_bytes()
  job={'model':'M','directory':str(d),'model_sha256':fp.digest(m/'model.json'),'rounds':0,'focus':''}
  with patch.object(fp.subprocess,'run',side_effect=subprocess.TimeoutExpired(['fake-discovery'],15))as call:
   try:fp.job_chunk(job,r,1)
   except subprocess.TimeoutExpired:pass
   else:raise AssertionError('timeout not propagated')
   assert call.call_args.kwargs['timeout']==15.0
  assert (d/'checkpoint.tree').read_bytes()==old and (d/'STATUS.json').read_bytes()==old_status and not (d/'next.tree').exists()
  (d/'checkpoint.tree').write_text('S 0\nA 1\nO\n')
  with (r/'payload').open('wb')as out:fp.copy_focused_payload(d/'checkpoint.tree',[(0,0)],out)
  assert (r/'payload').read_text()=='A 1\n'
  rejected=0
  for text in ['S 1\nA 1\nO\n','S 0\nA 1\nA 4\n','S 0\nA 1\nO\nO\n']:
   (d/'checkpoint.tree').write_text(text)
   try:
    with (r/'payload').open('wb')as out:fp.copy_focused_payload(d/'checkpoint.tree',[(0,0)],out)
   except ValueError:rejected+=1
   else:raise AssertionError('bad ownership accepted')
 return {'status':'V35_CHECKPOINT_TIMEOUT_AND_OWNERSHIP_PASS','forced_timeout_preserved_old_checkpoint':True,'unaccepted_next_removed':True,'alpha_terminal_preserved':True,'bad_ownership_rejected':rejected,'real_40_worker_run_claimed':False}
if __name__=='__main__':print(json.dumps(verify(),indent=2))
