from pathlib import Path
import sys,json
R=Path(__file__).resolve().parent
sys.path.insert(0,str(R/'data/deep'));import deep_math as dm
bp=dm.load_protocol(R/'data/deep')
out=[]
for s in json.loads((R/'SOURCE_REBUILD.json').read_text())['records']:
 out.append({'ordinal':s['ordinal'],'literal_inherited_safe_port':bp.fs.safe_port(s['aux_image'])})
(R/'LITERAL_PORT_CHECK.json').write_text(json.dumps(out,indent=2)+'\n')
