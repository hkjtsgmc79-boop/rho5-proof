"""Cheap exact necessary-condition census from already ancestor-verified original B17 boxes."""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
from itertools import product
import argparse,gzip,hashlib,json,os
ROOT=Path(__file__).resolve().parent

def main():
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 model=json.loads((ROOT/'models/B17_FULL.json').read_text());order=model['frame_order'];assert [order.index(n)for n in ('k','u0','v0')]==[0,5,11]
 frames=[json.loads(s)for s in gzip.open(ROOT/'inherited/OPEN_FRONTIERS.jsonl.gz','rt')]
 kc=Q('2.074468372');uc=Q(1);vc=Q('-0.581690673');results={}
 import r53_port as port
 for center in port.centers():
  actual=dict(zip(port.tb.X_NAMES,center));assert (actual['k'],actual['u0'],actual['v0'])==(kc,uc,vc)
 for rho in (Q(1,1250),Q(3,2500),Q(3,1000)):
  rows=[];counts=Counter()
  for r in frames:
   k,u,v=[tuple(map(Q,r['box'][i]))for i in (0,5,11)]
   dist=lambda z,c:max(Q(0),z[0]-c,c-z[1]);ks=dist(k,kc);choices=[]
   for tr,sg in product((False,True),(-1,1)):
    uu,vv=(v,u)if tr else(u,v)
    if sg==-1:uu=(-uu[1],-uu[0]);vv=(-vv[1],-vv[0])
    ds=[ks,dist(uu,uc),dist(vv,vc)]
    choices.append({'transpose':tr,'third_axis_sign':sg,'distance_lower':str(max(ds)),'outside_coordinates':[n for n,d in zip(('k','u0','v0'),ds)if d>rho]})
   excluded=all(Q(c['distance_lower'])>rho for c in choices)
   cat='k_already_excluded'if ks>rho else'additional_u0_v0_excluded'if excluded else'necessary_condition_only'
   counts[cat]+=1;rows.append({'index':r['index'],'path':r['path'],'box':r['box'],'category':cat,'minimum_head_distance_lower':str(min(Q(c['distance_lower'])for c in choices)),'choices':choices})
  assert sum(counts.values())==754
  results[str(rho)]={'counts':dict(counts),'records':rows}
 result={'status':'R53_ORIGINAL_B17_K_U0_V0_NECESSARY_CONDITION_CENSUS','original_root_sha256':'4b72152fec20a58eff52ab6e93a8fd082fc85a28722d762412c0c5fc17abc707','frame_order':order,'centers':{'k':str(kc),'u0':str(uc),'v0':str(vc)},'radii':results,'scope':'All four centers have identical k/u0/v0. R, D and sorting preserve these head entries. REP only swaps u0/v0 and applies their common third-axis sign. Interval disjointness excludes entry into these fixed cubes, not complete physical sources or other transports that change the first three rows/columns. No U41 replay or LP census performed here.'}
 parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,default=ROOT/'HEAD_CENSUS754.json');args=parser.parse_args()
 args.out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v['counts']for k,v in results.items()},indent=2))
if __name__=='__main__':main()
