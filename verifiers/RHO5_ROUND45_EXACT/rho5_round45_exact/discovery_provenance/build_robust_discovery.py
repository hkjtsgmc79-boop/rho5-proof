"""Discovery-only numerical repair. Frozen models and exact acceptor are untouched."""
from pathlib import Path
import argparse, hashlib, json, subprocess
import frontier_parallel as fp

def main():
    ap=argparse.ArgumentParser();ap.add_argument('root',type=Path);a=ap.parse_args()
    root=a.root.resolve();work=root/'working';out=root/'robust_proposal';out.mkdir(exist_ok=True)
    old=(work/'source/mc_simplex_dual.hpp').read_text()
    header=old.replace('double','long double').replace('EPS=1e-9','EPS=1e-12L')
    # Keep the old public double API; only tableau arithmetic and pivots use 80-bit.
    header=header.replace('Simplex(const std::vector<std::vector<long double>>&A,const std::vector<long double>&b,const std::vector<long double>&c)',
                          'Simplex(const std::vector<std::vector<double>>&A,const std::vector<double>&b,const std::vector<double>&c)')
    header=header.replace('std::vector<long double> dual()const { std::vector<long double> y(m);',
                          'std::vector<double> dual()const { std::vector<double> y(m);')
    header=header.replace('long double solve(std::vector<long double>&x)', 'double solve(std::vector<double>&x)')
    header=header.replace('if(B[i]<n)x[B[i]]=', 'if(B[i]>=0&&B[i]<n)x[B[i]]=')
    source=fp.patch_focus((work/'source/discover.cpp').read_text())
    source=source.replace('#include "mc_simplex_dual.hpp"','#include "proposal_simplex.hpp"')
    old_condition='if(std::isfinite(ans)&&x.size()==NX)'
    validation='''bool valid=std::isfinite(ans)&&x.size()==NX;
 if(valid)for(int j=0;j<NX;j++)if(!std::isfinite(x[j])||x[j]<-1e-7||x[j]>1+1e-7){valid=false;break;}
 if(valid)for(size_t i=0;i<A.size();i++){
  long double dot=0,mag=1+std::abs(b[i]);
  for(int j=0;j<NX;j++){dot+=(long double)A[i][j]*x[j];mag+=std::abs((long double)A[i][j]*x[j]);}
  if(dot>(long double)b[i]+1e-8L*mag){valid=false;break;}
 }
 if(valid)'''
    assert source.count(old_condition)==1
    source=source.replace(old_condition,validation)
    source=source.replace(' || box.depth>=120','')
    source=source.replace('if(f.closed){emit_leaf(out,f.w);return;}',
                          'if(f.closed){emit_leaf(out,f.w);return;}\n if(box.depth>=170){out<<"O\\n";opens++;return;}')
    for name,pin in fp.PINS.items():
        model=work/'models'/name
        assert fp.digest(model/'model.json')==pin
        d=out/name;d.mkdir(exist_ok=True)
        (d/'proposal_simplex.hpp').write_text(header);(d/'discover_robust.cpp').write_text(source)
        with (d/'COMPILE.log').open('w') as log:
            subprocess.run(['g++','-O3','-std=c++17','-I'+str(model),str(d/'discover_robust.cpp'),'-o',str(d/'discover_robust')],stdout=log,stderr=subprocess.STDOUT,check=True)
    fp.write_json(out/'DISCOVERY_REPAIR_RECEIPT.json',{
        'status':'NUMERICAL_PROPOSAL_ONLY_NO_NEW_ACCEPTANCE_RULE',
        'changes':['80-bit simplex tableau, EPS 1e-12','validate scaled LP point bounds and rows before using split scores',
                   'exclude artificial variable from solution indexing','attempt existing exact rank and weighted leaves before depth cap',
                   'discovery depth cap 170; original exact verifier cap stays 180'],
        'source_sha256':hashlib.sha256(source.encode()).hexdigest(),
        'simplex_sha256':hashlib.sha256(header.encode()).hexdigest(),
        'frozen_model_pins':fp.PINS,
        'exact_sources':{n:fp.digest(work/'source'/n) for n in ('mc_exact_kernel.hpp','rankone_oracle.hpp','mc_verify.cpp')}
    })
    print(json.dumps({'status':'ROBUST_PROPOSAL_BINARIES_READY','directory':str(out)}),flush=True)

if __name__=='__main__':main()
