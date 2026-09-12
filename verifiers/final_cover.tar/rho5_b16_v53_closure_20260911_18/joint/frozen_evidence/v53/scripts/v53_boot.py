from pathlib import Path
from fractions import Fraction as Q
import sys,json,hashlib,copy,time,os
sys.dont_write_bytecode=True
sys.setrecursionlimit(10000)
ROOT=Path(__file__).resolve().parent
INPUT=Path(os.environ.get('V53_INPUT', str(ROOT.parent/'v53_input'))).resolve()
DEP=INPUT/'B_STRUCTURE_15/frozen/deep'
sys.path.insert(0,str(DEP))
import deep_math as dm
bp=dm.load_protocol(DEP)
sys.path.insert(0,str(INPUT/'alpha_support'))
import alpha_cover as ac
ac.configure(INPUT/'alpha_support/b14_runtime')
centers=ac.fixed_centers()
ORDER='k r s t A B c d p e beta u0 u1 u2 x0 x1 x2 v0 v1 v2 q0 q1 q2 F'.split()
PATH='1001110110011011111'
PARENT=INPUT/'previous_source_snapshot/alpha_v1/sources/9d7f10cf242dddc51c6fd5a03fed4adf9f4084bb9c3584e801f4693ce093f780_435003_parent.json'
PROJECTION=INPUT/f'latest_sources/435003_{PATH}_projection.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def jsha(v):return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
def save(p,x):
 p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n');t.replace(p)
def require(x,s):
 if not x:raise ValueError(s)
def at(tree,path):
 for bit in path:
  t=tree['terminal'];require(t['kind']=='S','bad path');tree=t['left' if bit=='0' else 'right']
 return tree

def source(path=PATH,projection=PROJECTION):
 start=time.monotonic();par=json.loads(PARENT.read_text());cert=json.loads(Path(projection).read_text())
 require(sha(PARENT)=='9d7f10cf242dddc51c6fd5a03fed4adf9f4084bb9c3584e801f4693ce093f780','parent bytes')
 expected=bp.binding(par)
 require(set(cert)==set(expected)|{'profile','tree'},'schema')
 if cert['rule']==dm.OLD_RULE:
  man=json.loads((DEP/'runtime/DEEP500_MANIFEST.json').read_text());dm.validate_legacy_binding(par,cert,man['legacy_rule_identity'],bp)
 else:
  require({k:cert[k] for k in expected}==expected,'binding');dm.counts(cert['tree'])
 out,stats=bp.prefix_image(par,cross_check=True);node=cert['tree'];visits=[];lineage=[]
 for dep in range(len(path)+1):
  out=bp.db.common_contract(out,profile=cert['profile'])
  for wave in node['waves']:out=bp.db.apply_wave(out,wave,profile=cert['profile'],cross_check=True)
  require(out['status']=='BOUNDED','source unexpectedly empty')
  t=node['terminal'];entry={'depth':dep,'path':path[:dep],'waves':len(node['waves']),'bounds':sum(map(len,node['waves'])),'waves_sha256':jsha(node['waves']),'image_sha256':jsha(out['aux_image']),'kind':t['kind']}
  visits.append(entry)
  if dep==len(path):
   require(t=={'kind':'O'},'source not O');break
  require(t['kind']=='S' and type(t['axis']) is int and 0<=t['axis']<24,'ancestor split')
  axis=t['axis'];lo,hi=map(Q,out['aux_image'][axis]);mid=(lo+hi)/2;require(lo<mid<hi,'nonproper split');side=path[dep]
  entry.update(axis=axis,side=side,midpoint=str(mid));lineage.append({'waves':copy.deepcopy(node['waves']),'axis':axis,'side':side})
  aux=copy.deepcopy(out['aux_image']);aux[axis][1 if side=='0' else 0]=str(mid);out={'status':'BOUNDED','aux_image':aux};node=t['left' if side=='0' else 'right']
 res={'parent_index':435003,'path':path,'parent_raw_sha256':sha(PARENT),'projection_raw_sha256':sha(projection),'binding':expected,'profile':cert['profile'],'aux_image':out['aux_image'],'image_sha256':jsha(out['aux_image']),'prefix_stats':stats,'visits':visits,'lineage':lineage,'target_waves':node['waves'],'seconds':time.monotonic()-start}
 return res
if __name__=='__main__':
 x=source();save(ROOT/'source_rebuilt.json',x);print('SOURCE',x['image_sha256'],'seconds',x['seconds'],flush=True)
 for n,(lo,hi) in zip(ORDER,x['aux_image']):print(n, '%.12g %.12g width %.7g'%(float(Q(lo)),float(Q(hi)),float(Q(hi)-Q(lo))),flush=True)
 t=time.monotonic();port=ac.discover_port(x['aux_image'],centers);print('PORT',port,'seconds',time.monotonic()-t,flush=True)
 if port:save(ROOT/'direct_port.json',{'proposal':port,'verification':ac.verify_port(x['aux_image'],port,centers)})
