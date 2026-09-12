"""Optional proof discovery.  Not imported by the acceptance path.
Requires scipy and numpy in addition to the verifier's dependencies.
Different solver versions may discover different valid trees; certification is
by verify.py, not by matching the optimizer's output or a floating residual.
"""
from pathlib import Path
import argparse,concurrent.futures,subprocess,sys
ROOT=Path(__file__).resolve().parent;KEYS=['PX1','PX2','PY1','PY2','EX1','EX2']
def one(key,cap):
 subprocess.run(['g++','-std=c++17','-O2','-fPIC','-shared','-I'+str(ROOT/'cpp'),f'-DMODEL_HEADER="{key}.hpp"',str(ROOT/'cpp/linearize.cpp'),'-o',str(ROOT/f'linear_{key}.so')],check=True)
 subprocess.run([sys.executable,str(ROOT/'generate_lp.py'),key,str(cap)],check=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--jobs',type=int,default=4);p.add_argument('--node-limit',type=int,default=100000);a=p.parse_args()
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs)as ex:list(ex.map(lambda k:one(k,a.node_limit),KEYS))
 print('Discovery completed. Regenerated proof files must be accepted; refresh a separate manifest only after validation.')
