#!/usr/bin/env python3
"""Stage immutable model/reference files and versioned high-value additions only."""
from pathlib import Path
import hashlib,json,shutil
OWN=Path(__file__).resolve().parent
SOURCE=OWN/'working_native';TARGET=OWN/'working_high_value';ADDITIONS=OWN/'high_value_additions'
manifest=json.loads((SOURCE/'NATIVE_SOURCE_MANIFEST.json').read_text())
TARGET.mkdir()
for name,digest in manifest['files'].items():
    source=SOURCE/name;assert hashlib.sha256(source.read_bytes()).hexdigest()==digest,name
    out=TARGET/name;out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,out)
for source in ADDITIONS.iterdir():
    if source.is_file() and source.suffix in ('.cpp','.py','.md'):shutil.copy2(source,TARGET/source.name)
rule={'schema':'B17_HIGH_VALUE_ENCLOSURE_RULE_V1','enclosure':'high_value_v1','iterations':8,
      'model_sha256':manifest['model_sha256'],'parent_static_manifest_sha256':manifest['parent_static_manifest_sha256'],
      'old_leaf_semantics':'Missing enclosure tag always uses unmodified V37 canonical image and rows',
      'scope':'Necessary inequalities for the same physical canonical maximum with actual F >= gamma; gamma is a lower localization trigger',
      'dependencies':['p-e*beta<=1','0<=e,beta<=1','0<=s,t<=r','r>0','r*F=r*r+s*t','F<=4*p'],
      'universal_rows':106,'shared_products':38,'unknown_versions':'reject','sign_ambiguity':'retain wide interval',
      'theorem_sha256':hashlib.sha256((TARGET/'HIGH_VALUE_CONTRACTION_THEOREM.md').read_bytes()).hexdigest(),
      'whole_B_closed':False,'macro_ledger':'14/15'}
(TARGET/'HIGH_VALUE_RULE.json').write_text(json.dumps(rule,indent=2)+'\n')
print(json.dumps({'status':'HIGH_VALUE_PACKAGE_STAGED','directory':str(TARGET),'parent_manifest_files':len(manifest['files'])}))
