#!/usr/bin/env python3
"""Build a small review handoff, never claim omitted trees were replayed remotely."""
from pathlib import Path
import json,argparse,hashlib,subprocess,sys,zipfile
from verify_campaign import digest,ROOT

def main():
 p=argparse.ArgumentParser();p.add_argument('--state',type=Path,default=ROOT/'campaign/CURRENT_STATE.json');p.add_argument('--out',type=Path,default=ROOT/'v35_local_light.zip');a=p.parse_args()
 # A fresh local replay is mandatory. Open roots are explicitly allowed but never credited.
 r=subprocess.run([sys.executable,str(ROOT/'verify_campaign.py'),str(a.state),'--allow-open'],text=True,capture_output=True)
 if r.returncode:raise RuntimeError(r.stdout+r.stderr)
 state=json.loads(a.state.read_text());fresh=json.loads(r.stdout)
 items={};omitted=[]
 for n,record in state['models'].items():
  tree=Path(record['tree']);omitted.append({'name':n,'tree_bytes':tree.stat().st_size,'tree_sha256':digest(tree),'scope':fresh['models'][n]['scope'],'open':fresh['models'][n]['open']})
  items[f'models/{n}/model.json']=(ROOT/'models'/n/'model.json').read_bytes()
 for pattern in ('source/*','theory/*','reference/*.md','reference/parent_models/*.json','reference/direct_f_parent_models/*.json','reference/flow_tube_parent_models/*.json'):
  for f in ROOT.glob(pattern):
   if f.is_file():items[str(f.relative_to(ROOT))]=f.read_bytes()
 for name in ('build_models.py','build_models_original.py','build_models_flow_parent.py','DIRECT_F_RULE.json','WEIGHTED_HEIGHT_RULE.json','WEIGHTED_HEIGHT_THEOREM.md','DIRECT_F_THEOREM.md','FLOW_TUBE_THEOREM.md','factor_feasibility.py','physical_packets.py','verify_task.py','verify_campaign.py','reference/r45_build_model.py','alpha_ports.py','local_model.py','verify_local_certificate.py','local_wall_certificate.json','alpha.json','THEORY.md','REPORT.md','LOCAL_RUN.md','control_witnesses.json','strict_offwall_control.json','native.py'):
  items[name]=(ROOT/name).read_bytes()
 items['FRESH_LOCAL_REPLAY_RESULT.json']=json.dumps(fresh,indent=2).encode()
 items['CURRENT_STATE.json']=json.dumps(state,indent=2).encode()
 items['READ_FIRST.md']=b'This is a light review handoff. Complete trees are omitted. The saved replay receipts are local computation records, not a remote replay of missing trees. Open roots, if any, are explicitly unpaid.\n'
 manifest={'purpose':'review-only; full trees omitted','omitted_trees':omitted,'files':{n:hashlib.sha256(b).hexdigest()for n,b in items.items()}}
 a.out.parent.mkdir(parents=True,exist_ok=True)
 with zipfile.ZipFile(a.out,'w',zipfile.ZIP_DEFLATED,compresslevel=9)as z:
  for n,b in sorted(items.items()):z.writestr(n,b)
  z.writestr('LIGHT_MANIFEST.json',json.dumps(manifest,indent=2))
 print(json.dumps({'status':'LIGHT_HANDOFF_SAVED','file':str(a.out),'bytes':a.out.stat().st_size,'sha256':digest(a.out),'open_by_model':{n:x['open']for n,x in fresh['models'].items()}}))
if __name__=='__main__':main()
