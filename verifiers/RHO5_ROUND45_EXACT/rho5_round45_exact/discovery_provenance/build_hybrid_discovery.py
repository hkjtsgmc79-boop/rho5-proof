"""Validated fast proposals with precise fallback. No exact-acceptance changes."""
from pathlib import Path
import json, subprocess, sys
import frontier_parallel as fp

root=Path(sys.argv[1]).resolve();name='II210_214';out=root/'hybrid_proposal'/name;out.mkdir(parents=True)
prior=root/'robust_proposal'/name;model=root/'working/models'/name
slow=(prior/'discover_robust.cpp').read_text();start=slow.index('Found solve_box(');end=slow.index('\nstd::string focus_path;')
function=slow[start:end]
fast=function.replace('Found solve_box(', 'Found solve_box_fast(').replace('Simplex lp(', 'FastSimplex lp(')
precise=function.replace('Found solve_box(', 'Found solve_box_precise(')
wrapper='''unsigned long long fast_calls=0,precise_calls=0;
Found solve_box(const EBox& box){
 fast_calls++;Found first=solve_box_fast(box);
 if(first.closed||first.val.size()==NX)return first;
 precise_calls++;return solve_box_precise(box);
}
'''
source=slow[:start]+fast+precise+wrapper+slow[end:]
source=source.replace('#include "proposal_simplex.hpp"','#include "proposal_simplex.hpp"\n#include "fast_simplex.hpp"')
header=(root/'working/source/mc_simplex_dual.hpp').read_text().replace('class Simplex','class FastSimplex').replace(' Simplex(', ' FastSimplex(')
header=header.replace('if(B[i]<n)x[B[i]]=', 'if(B[i]>=0&&B[i]<n)x[B[i]]=')
(out/'fast_simplex.hpp').write_text(header);(out/'proposal_simplex.hpp').write_bytes((prior/'proposal_simplex.hpp').read_bytes())
(out/'discover_hybrid.cpp').write_text(source)
with (out/'COMPILE.log').open('w') as log:
 subprocess.run(['g++','-O3','-std=c++17','-I'+str(model),str(out/'discover_hybrid.cpp'),'-o',str(out/'discover_hybrid')],stdout=log,stderr=subprocess.STDOUT,check=True)
fp.write_json(out/'HYBRID_PROPOSAL_RECEIPT.json',{'status':'VALIDATED_FAST_DISCOVERY_WITH_PRECISE_FALLBACK',
 'model_sha256':fp.digest(model/'model.json'),
 'source_sha256':fp.digest(out/'discover_hybrid.cpp'),'fast_simplex_sha256':fp.digest(out/'fast_simplex.hpp'),
 'precise_simplex_sha256':fp.digest(out/'proposal_simplex.hpp'),
 'exact_sources':{n:fp.digest(model/n) for n in ('mc_verify.cpp','mc_exact_kernel.hpp','rankone_oracle.hpp')},
 'mathematical_rule_changes':False,'point_validation':'same scaled bounds and all LP rows as robust proposal',
 'fallback':'When the fast solver has neither an exact integer contradiction nor a validated LP point, use the validated long-double solver.'})
print(json.dumps({'status':'HYBRID_DISCOVERY_COMPILED','directory':str(out)}),flush=True)
