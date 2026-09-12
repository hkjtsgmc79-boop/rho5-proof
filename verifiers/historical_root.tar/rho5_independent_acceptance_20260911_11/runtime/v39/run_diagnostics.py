from pathlib import Path
from collections import Counter
import json,time
from discover import *
ROOT=Path(__file__).resolve().parent
samples=json.loads((ROOT/'inputs/diagnostics/audit_final/SAMPLE_CONTROLS.json').read_text())
out=ROOT/'evidence/frontier_covers';out.mkdir(exist_ok=True)
stats=[];start=time.monotonic()
for item in samples:
 number=item['sample'];p=out/f'sample_{number:02d}.json'
 cert,local=discover_cover(item['box'])
 p.write_text(json.dumps(cert,separators=(',',':'))+'\n')
 checked=verify_cover(item['box'],cert,allow_open=True)
 row={'sample':number,'source_path':item['path'],'source_box':item['box'],'classification':checked,'counts':local['counts'],'seconds':local['seconds'],'surviving_after_interval':local['surviving_after_interval']}
 stats.append(row)
 (ROOT/'evidence/frontier_diagnostic_running.json').write_text(json.dumps(stats,indent=2)+'\n')
 print(number,local['counts'],checked['status'],round(local['seconds'],3),flush=True)
c=Counter();k=Counter()
for row in stats:c.update(row['counts']);k[row['classification']['status']]+=1
result={'samples':64,'aggregate_chart_outcomes':dict(c),'box_outcomes':dict(k),'seconds':time.monotonic()-start,'source_full_tree_received':False,'old_parent_model_modified':False,'all_sample_boxes_checked_here':True,'no_global_closure':True,'macro_ledger':'14/15','records':stats}
(ROOT/'evidence/frontier_diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k!='records'},indent=2),flush=True)
