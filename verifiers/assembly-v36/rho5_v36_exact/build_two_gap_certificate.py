from pathlib import Path
from fractions import Fraction as Q
import json
from gap_model import NAMES,source
ROOT=Path(__file__).parent
x=json.loads((ROOT/'inputs/round47/source/local_wall_certificate.json').read_text());rows=source();cases=[]
for c in x['cases']:
 active=c['active_labels'];Co=[list(map(Q,row))for row in c['inverse_preconditioner']]
 N=[[rows[n].get((j,),Q(0))for j in (22,23)]for n in active]
 C=[row+[-sum(Co[i][a]*N[a][g]for a in range(21))for g in range(2)]for i,row in enumerate(Co)]
 C += [[Q(0)]*21+[Q(1),Q(0)],[Q(0)]*21+[Q(0),Q(1)]]
 cases.append({'case':c['case'],'center':c['center']+['0','0'],'active_labels':active+['sigma','tau'],'preconditioner':[[str(a)for a in row]for row in C]})
y={'schema':'V36_TWO_GAP_FLOW_V1','coordinate_order':list(NAMES),'fixed_coordinate':'p','outer_radius':'1/1250','inner_radius':'1/10000','speed_cap':'3','gain':'1/10','cases':cases}
(ROOT/'two_gap_certificate.json').write_text(json.dumps(y,indent=2)+'\n')
