from pathlib import Path
from zipfile import ZipFile
import hashlib,json
import paths

def run():
 archive=paths.ROOT/'inputs/RHO5_ROUND48_B17_LIGHT.zip'
 with ZipFile(archive)as z:
  prefix='rho5_round48_b17/'
  names=z.namelist()
  if len(set(names))!=len(names):raise ValueError('Duplicate archive member')
  manifest=json.loads(z.read(prefix+'LIGHT_INTEGRITY.json'))['files']
  for name,want in manifest.items():
   if hashlib.sha256(z.read(prefix+name)).hexdigest()!=want:raise ValueError('Light archive mismatch '+name)
  for p in paths.FROZEN.rglob('*'):
   if not p.is_file()or '__pycache__'in p.parts:continue
   rel=p.relative_to(paths.FROZEN).as_posix()
   if p.read_bytes()!=z.read(prefix+rel):raise ValueError('Frozen dependency changed '+rel)
  a=json.loads(z.read(prefix+'receipts/FROZEN_ROOT_REPLAY.json'))
  b=json.loads(z.read(prefix+'receipts/FRACTION_COLD_REPLAY.json'))
  for key in ('tree_sha256','model_sha256','source_manifest_sha256','rule_sha256','nodes','contradictions','alpha_safe','open'):
   if a[key]!=b[key]:raise ValueError('Receipt identity/count mismatch '+key)
  assert a['nodes']==749693 and a['open']==17655
  assert prefix+'campaign_native/B17_COMPOSED_ROOT.json'not in names
 return {'light_file_hashes_checked':len(manifest),'local_receipts_agree':True,'round48_full_tree_received':False,'round48_full_tree_replayed_here':False,'light_zip_sha256':hashlib.sha256(archive.read_bytes()).hexdigest()}
if __name__=='__main__':print(json.dumps(run(),indent=2))
