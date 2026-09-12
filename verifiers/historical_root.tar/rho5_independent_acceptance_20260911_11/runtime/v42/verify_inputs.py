from pathlib import Path
import json,subprocess,sys
from _v42_bootstrap import prepare,sha

def run():
 p=prepare();out=p['root']/'B02_replayed.json'
 subprocess.run([sys.executable,str(p['b02']/'b_structure_02.py'),'--output',str(out)],check=True,capture_output=True,text=True)
 expected=p['b02']/'evidence/verification.json'
 if sha(out)!=sha(expected):raise ValueError('Original B02 replay differs from supplied evidence')
 return dict(status='V42_RECEIVED_BYTES_AND_B02_REPLAY_PASS',handoff_hash_members=p['manifest_count'],
     B02_replay_sha256=sha(out),unreceived_Round51_full_tree_replayed=False)
if __name__=='__main__':print(json.dumps(run()))
