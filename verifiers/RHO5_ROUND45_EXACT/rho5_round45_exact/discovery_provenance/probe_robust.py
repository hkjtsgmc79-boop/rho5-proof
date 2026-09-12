from pathlib import Path
import json, subprocess, sys
import frontier_parallel as fp

root=Path(sys.argv[1]).resolve();out=root/'robust_proposal/II210_214';model=root/'working/models/II210_214'
source=(root/'probe_box.cpp').read_text().replace('#include "discover.cpp"','#include "discover_robust.cpp"')
(out/'probe_robust.cpp').write_text(source)
subprocess.run(['g++','-O3','-std=c++17','-I'+str(model),str(out/'probe_robust.cpp'),'-o',str(out/'probe_robust')],check=True)
with (root/'diagnostics/probe_input.txt').open() as stream:
 p=subprocess.run([str(out/'probe_robust')],stdin=stream,capture_output=True,text=True,check=True)
(out/'PROBE_RAW.jsonl').write_text(p.stdout)
rows=list(map(json.loads,p.stdout.splitlines()));previous=json.loads((root/'diagnostics/FRONTIER_DIAGNOSTIC.json').read_text())
invalid=[]
for rec,r in zip(previous['samples'],rows):
 if r['values']:
  for j,name in enumerate(rec['box_display']):
   lo,hi=rec['box_display'][name];v=r['values'][j]
   if not lo-1e-6<=v<=hi+1e-6:invalid.append([r['label'],name,v,lo,hi])
result={'status':'DISCOVERY_PROPOSAL_DIAGNOSTIC_NO_HEIGHT_CREDIT','count':len(rows),
 'rank_closable':sum(r['rank_code']>=0 for r in rows),'integer_dual_closable':sum(r['integer_dual_closed'] for r in rows),
 'any_exact_closable':sum(r['rank_code']>=0 or r['integer_dual_closed'] for r in rows),
 'validated_float_points':sum(bool(r['values']) for r in rows),'invalid_box_points':invalid}
fp.write_json(out/'PROBE_RESULT.json',result);print(json.dumps(result),flush=True)
assert not invalid
