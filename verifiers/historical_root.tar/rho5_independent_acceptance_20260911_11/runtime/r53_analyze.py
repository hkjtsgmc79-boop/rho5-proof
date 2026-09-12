from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
import argparse,hashlib,json,os
import r53_port as port
ROOT=Path(__file__).resolve().parent
HEAD=('k','p','e','beta','u0','x0','v0','q0')
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def analyze(aux):
 source=port.tb.load_box(aux);candidates=[]
 for tr in (False,True):
  for sg in port.product((-1,1),repeat=3):
   z=port.tb.diagonal(port.tb.transpose(source)if tr else source,sg)
   for j,cen in enumerate(port.centers()):
    cmap=dict(zip(port.tb.X_NAMES,cen));dl={n:max(Q(0),z[n].lo-cmap[n],cmap[n]-z[n].hi)for n in HEAD};du={n:(z[n]-cmap[n]).abs_upper()for n in HEAD}
    candidates.append({'transpose':tr,'signs':list(sg),'case':j,'head_distance_lower':str(max(dl.values())),'head_distance_upper':str(max(du.values())),'outside_coordinates':[n for n in HEAD if dl[n]>port.RHO],'head_intervals':{n:z[n].data()for n in HEAD},'coordinate_distance_lower':{n:str(x)for n,x in dl.items()}})
 best=min(candidates,key=lambda c:Q(c['head_distance_lower']));all_out=all(Q(c['head_distance_lower'])>port.RHO for c in candidates)
 return {'all_R_and_D_targets_excluded_by_preserved_head':all_out,'minimum_head_distance_lower':best['head_distance_lower'],'best_candidate':best,'candidates':candidates,'F_upper':aux[23][1],'source_width_sum':str(sum(Q(b)-Q(a)for a,b in aux)),'theorem_scope':'Exact interval exclusion of all 16 representations and four certified cubes for R and every qualified subset of D, by coordinates preserved by either tail transport; not physical source infeasibility.'}
if __name__=='__main__':
 if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
 parser=argparse.ArgumentParser();parser.add_argument('--pilot',type=Path,default=ROOT/'pilot16');parser.add_argument('--receipt',type=Path,default=ROOT/'receipts/V43_REPLAY.json');parser.add_argument('--out',type=Path,default=ROOT/'pilot16/HEAD_OBSTRUCTIONS.json');args=parser.parse_args()
 rows=[]
 for p in sorted(args.pilot.glob('result_*.json')):
  r=read(p);rows.append({'index':r['index'],'scope':'unconditional','source_receipt_sha256':sha(p),**analyze(r['endpoint']['aux_image'])})
 evidence=read(args.receipt)
 for r in evidence['R52_diagnostic']['records']:
  for c in r['children']:rows.append({'index':r['index'],'scope':c['label'],'source_receipt_sha256':sha(args.receipt),**analyze(c['meet_endpoint'])})
 result={'status':'R53_TRANSPORT_INVARIANT_HEAD_AUDIT','preserved_coordinates':HEAD,'radius':str(port.RHO),'records':rows,'unconditional_excluded':sum(r['scope']=='unconditional'and r['all_R_and_D_targets_excluded_by_preserved_head']for r in rows),'conditional_excluded':sum(r['scope']!='unconditional'and r['all_R_and_D_targets_excluded_by_preserved_head']for r in rows),'whole_B_closed':False}
 args.out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items()if k!='records'},indent=2))
 for r in rows:print(json.dumps({'index':r['index'],'scope':r['scope'],'lower_distance':r['minimum_head_distance_lower'],'best_outside_coordinates':r['best_candidate']['outside_coordinates']}))
