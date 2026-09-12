#!/usr/bin/env python3
"""Optional discovery from the 13 inherited frontiers, in a NEW output directory.
Produces new trees, not promised to be byte-identical to the delivered ones.
Always run the independent acceptance afterward; an OPEN record is not success.
"""
from pathlib import Path
import os,sys,argparse,subprocess,shutil,json,ctypes as C
BASE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);ap.add_argument('--front',type=int);ap.add_argument('--seconds-per-front',type=int,default=1800);ap.add_argument('--max-nodes',type=int,default=300000);a=ap.parse_args()
    out=Path(a.output).resolve()
    if out.exists():raise FileExistsError('Use a new output directory; delivered certificates are never overwritten')
    out.mkdir(parents=True)
    cxx=os.environ.get('CXX','g++');flag='-dynamiclib' if sys.platform=='darwin' else '-shared'
    subprocess.run([cxx,'-O3','-std=c++17',flag,'-fPIC',str(BASE/'eval.cpp'),'-o',str(BASE/'libeval.so')],check=True)
    subprocess.run([cxx,'-O3','-std=c++17',flag,'-fPIC',str(BASE/'eval_taylor.cpp'),'-o',str(BASE/'libtaylor.so')],check=True)
    import numpy as np
    import discover_v28 as d
    oldeval=d.evaluate;oldsolve=d.solve
    lib=C.CDLL(str(BASE/'libtaylor.so'));ptr=np.ctypeslib.ndpointer(dtype=np.int64,flags='C_CONTIGUOUS')
    lib.eval_taylor.argtypes=[ptr,ptr,C.c_int64,C.c_int64,ptr,ptr]
    def evaluate(lo,hi,f):
        bd,rows=oldeval(lo,hi,f);bt=np.zeros((37,2),dtype=np.int64);rt=np.zeros((37,7),dtype=np.int64)
        if lib.eval_taylor(np.array(lo,dtype=np.int64),np.array(hi,dtype=np.int64),f.numerator,f.denominator,bt,rt):raise ArithmeticError('Taylor interval overflow')
        if not np.array_equal(bd,bt):raise ArithmeticError('natural-interval mismatch')
        return bd,np.vstack([rows[:35],rt[:35]]+([rows[35:36],rt[35:36]] if len(rows)==36 else []))
    def solve(lo,hi,f,do_contract=True):
        ans=oldsolve(lo,hi,f,do_contract)
        if ans:ans['mode']='MT'
        return ans
    d.evaluate=evaluate;d.solve=solve
    (out/'RHO5_V26_REBUILT').mkdir()
    cp=BASE/'RHO5_V26_REBUILT/global_localization_partial_checkpoint.json'
    shutil.copy2(cp,out/'RHO5_V26_REBUILT'/cp.name)
    d.BASE=out;p=json.loads(cp.read_text());fronts=[int(x['node']) for x in p['open_frontier']]
    if a.front is not None:
        if a.front not in fronts:raise ValueError('Unknown inherited frontier')
        fronts=[a.front]
    results=[d.run_root(n,a.max_nodes,a.seconds_per_front) for n in fronts]
    (out/'discovery_results.json').write_text(json.dumps(results,indent=2))
    print('DISCOVERY FINISHED. This is not independent acceptance. Check every OPEN count and replay.')
if __name__=='__main__':main()
