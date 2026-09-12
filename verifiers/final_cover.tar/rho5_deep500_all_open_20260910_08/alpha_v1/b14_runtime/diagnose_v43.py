from pathlib import Path
import sys,json
from fractions import Fraction as Q
R=Path(__file__).resolve().parent
sys.path.insert(0,str(R/'support'));sys.path.insert(0,str(R))
from exact_interval import serial
import structural_rules as sr
from transport_local import local_candidates
centers=[[Q(s)for s in c]for c in json.loads((R/'centers.json').read_text())]
out=[]
for rec in json.loads((R/'SOURCE_REBUILD.json').read_text())['records']:
 a=local_candidates(sr.image(rec['aux_image']),centers)
 best=min(a,key=lambda r:r['max_budget'])
 print(rec['ordinal'],rec['index'],rec['absolute_depth'],best['rep'],best['status'],float(best['max_budget']),[(b['branch'],b['center'],float(b['distance']),float(b['loss_upper']))for b in best['branches']])
 out.append({'ordinal':rec['ordinal'],'index':rec['index'],'path':rec['path'],'projection_sha256':rec['projection_sha256'],'image_sha256':rec['image_sha256'],'best':best})
(R/'V43_APPLICATION.json').write_text(json.dumps(serial(out),ensure_ascii=False,indent=2)+'\n')
