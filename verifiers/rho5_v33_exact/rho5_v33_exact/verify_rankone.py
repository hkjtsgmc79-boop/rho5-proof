#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import json,random,subprocess,tempfile
from rankone_interval import impossible,stage_tail_intervals,exclusion,mul
from native_checker import native,physical_slacks
ROOT=Path(__file__).resolve().parent

def main():
    # Two exact, isolated-layer obstructions. Neither is a physical 5x5 source.
    H=[1,1,1,-1];D=[Q(5,4)*h for h in H];Z=[-Q(1,4)*h for h in H]
    assert all(abs(d+z)<=1 for d,z in zip(D,Z))
    assert all(2-sum(ep[i]*Z[i] for i in range(4))>=0 for ep in product((-1,1),repeat=4) if ep[0]*ep[1]*ep[2]*ep[3]==-1)
    assert Z[0]*Z[3]-Z[1]*Z[2]==-Q(1,8)
    assert impossible(stage_tail_intervals(D,1))
    assert impossible(stage_tail_intervals([Q(19,10)]*3+[-Q(9,10)],1))
    # Boundary determinant products meet at zero: no strict exclusion permitted.
    assert not impossible([(-1,0),(0,1),(0,1),(0,0)])
    assert not impossible([(0,0)]*4)
    rng=random.Random(320908);safe=0
    for _ in range(250):
        a=[Q(rng.randrange(-16,17),16) for _ in range(2)]
        b=[Q(rng.randrange(-16,17),16) for _ in range(2)]
        z=[a[i]*b[j] for i,j in product(range(2),repeat=2)]
        boxes=[(t-Q(rng.randrange(4),64),t+Q(rng.randrange(4),64)) for t in z]
        assert not impossible(boxes);safe+=1
    # Native physical source regression: no high-source/root assertion is made.
    records=json.loads((ROOT/'logs/transport_verification.json').read_text())['records']
    boxcases=[]
    for rec in records:
        st=native(rec['maximal_matrix']);assert min(v for _,v in physical_slacks(st))>=0
        D=st['D'];k=D[0][0];H0=[[D[i][j]-D[i][0]*D[0][j]/k for j in (1,2)] for i in (1,2)]
        vals=[k,H0[0][0],H0[1][1],D[0][1],D[0][2],D[1][0]/k,D[2][0]/k,st['p'],st['e'],st['beta']]+st['u']+st['x']+st['v']+st['q']+[Q(0)]
        assert exclusion(vals,vals)==-1
        boxcases.append((vals,vals))
    # C++ vs Fraction on exact integer-grid boxes. Independent arithmetic,
    # but both implement the explicit documented interval contractor.
    model=ROOT/'models/I214'
    with tempfile.TemporaryDirectory() as td:
        d=Path(td)
        for f in ('mc_exact_model.hpp','mc_exact_kernel.hpp','rankone_oracle.hpp'):
            (d/f).write_bytes((model/f).read_bytes())
        cpp='''#include "rankone_oracle.hpp"\n#include <iostream>\nint main(){try{int n;if(!(std::cin>>n))return 1;while(n--){EBox b;for(int i=0;i<EV;i++)std::cin>>b.lo[i]>>b.hi[i];std::cout<<rankone_exclusion(b)<<"\\n";}}catch(const std::exception&e){std::cerr<<e.what();return 1;}}'''
        (d/'main.cpp').write_text(cpp)
        subprocess.run(['g++','-O2','-std=c++17','main.cpp','-o','test'],cwd=d,check=True)
        data=json.loads((model/'model.json').read_text());rootlo,roothi=data['root_numerators'];unit=10**9*2**128
        rng=random.Random(1332);inp=[];expect=[]
        for z in range(120):
            lo=[];hi=[]
            for i,(l,u) in enumerate(zip(rootlo,roothi)):
                den=2**rng.randrange(0,7);a=rng.randrange(den);b=rng.randrange(a+1,den+1)
                lo.append(l*2**128+(u-l)*2**128*a//den)
                hi.append(l*2**128+(u-l)*2**128*b//den)
            inp.append(' '.join(str(t) for pair in zip(lo,hi) for t in pair))
            expect.append(exclusion([Q(t,unit) for t in lo],[Q(t,unit) for t in hi]))
        res=subprocess.run([str(d/'test')],input=str(len(inp))+'\n'+'\n'.join(inp)+'\n',text=True,capture_output=True,check=True)
        got=list(map(int,res.stdout.split()));assert got==expect
    result={'status':'EXACT_RANKONE_INTERVAL_COMPONENTS_PASS','isolated_relaxation_obstructions':2,'rank_one_containment_tests':safe,'physical_sources_retained':len(records),'cpp_fraction_cross_checks':len(expect),'cross_check_exclusions':sum(t>=0 for t in expect),'no_global_height_claim':True}
    (ROOT/'logs/rankone_verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
