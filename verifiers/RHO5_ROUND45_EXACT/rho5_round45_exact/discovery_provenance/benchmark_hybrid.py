"""Bounded A/B comparison at frozen original-root open boxes; no height credit."""
from pathlib import Path
import json, subprocess, sys, time
import frontier_parallel as fp

root=Path(sys.argv[1]).resolve();name='II210_214';out=root/'hybrid_proposal'/name;model=root/'working/models'/name
data=json.loads((model/'model.json').read_text());state=json.loads((root/'parallel_robust_II210_214/CURRENT_STATE.json').read_text())['models'][name]
fronts=fp.collect_frontiers(state['tree'],data,name)
# Include wide and deeper currently remaining boxes and the original 88 regression boxes.
selected=[fronts[i] for i in sorted({j*(len(fronts)-1)//min(31,len(fronts)-1) for j in range(min(32,len(fronts)))})] if len(fronts)>1 else fronts
lines=[]
for i,e in enumerate(selected):lines.append('current_'+str(i)+' '+str(len(e['steps']))+' '+' '.join(str(z) for pair in zip(e['lo'],e['hi']) for z in pair))
old=(root/'diagnostics/probe_input.txt').read_text().splitlines()[1:]
lines+=['regression_'+line for line in old]
(out/'BENCH_INPUT.txt').write_text(str(len(lines))+'\n'+'\n'.join(lines)+'\n')
results={}
for variant,src in [('precise',root/'robust_proposal'/name/'discover_robust.cpp'),('hybrid',out/'discover_hybrid.cpp')]:
 probe=(root/'probe_box.cpp').read_text().replace('#include "discover.cpp"','#include "'+str(src)+'"')
 if variant=='hybrid':probe=probe.replace('}catch(const std::exception&e)', 'std::cerr<<"fast_calls="<<fast_calls<<" precise_calls="<<precise_calls<<std::endl;}catch(const std::exception&e)')
 path=out/(variant+'_probe.cpp');path.write_text(probe)
 subprocess.run(['g++','-O3','-std=c++17','-I'+str(model),str(path),'-o',str(out/(variant+'_probe'))],check=True)
 with (out/'BENCH_INPUT.txt').open() as stream:
  start=time.monotonic();p=subprocess.run([str(out/(variant+'_probe'))],stdin=stream,capture_output=True,text=True,check=True);elapsed=time.monotonic()-start
 (out/(variant+'_RAW.jsonl')).write_text(p.stdout);rows=list(map(json.loads,p.stdout.splitlines()))
 results[variant]={'seconds':elapsed,'count':len(rows),'exact_closable':sum(r['rank_code']>=0 or r['integer_dual_closed'] for r in rows),
  'validated_points':sum(bool(r['values']) for r in rows),'counters':p.stderr.strip()}
 print(json.dumps({'variant':variant,**results[variant]}),flush=True)
fp.write_json(out/'BENCH_RESULT.json',{'status':'DISCOVERY_PROPOSAL_BENCHMARK_NO_HEIGHT_CREDIT',
 'original_root_tree_sha256':state['tree_sha256'],'models_unchanged':True,'results':results})
