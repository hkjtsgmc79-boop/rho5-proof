from pathlib import Path
import json,hashlib
import build_models_original as parent
ROOT=Path(__file__).resolve().parent
def make_model(K,J,typ,branch='low'):
    data=parent.make_model(K,J,typ,branch)
    f=ROOT/'reference/parent_models'/f'{typ}_LOW_ALPHA.json'
    if data!=json.loads(f.read_text()):raise ValueError('Original V35 semantic parent changed')
    rule=json.loads((ROOT/'DIRECT_F_RULE.json').read_text())
    if rule['alpha_definition_sha256']!=hashlib.sha256((ROOT/'alpha.json').read_bytes()).hexdigest():raise ValueError('Rule alpha binding changed')
    data['parent_model_sha256']=hashlib.sha256(f.read_bytes()).hexdigest()
    data['source_version']='V35_CQG_ROUND47_FLOW_TUBE_2026-09-08'
    data['additional_alpha_rule_sha256']=hashlib.sha256((ROOT/'DIRECT_F_RULE.json').read_bytes()).hexdigest()
    data['legal_safe_terminal_codes']['6']='direct_F_upper<=alpha_lower'
    previous=ROOT/'reference/direct_f_parent_models'/f'{typ}_LOW_ALPHA.json'
    old=json.loads(previous.read_text())
    if any(old[k]!=data[k] for k in ('variables','root_numerators','root_denominator','rows','pairs','K','J','type','branch','target')):raise ValueError('Direct F parent geometry changed')
    data['previous_version_model_sha256']=hashlib.sha256(previous.read_bytes()).hexdigest()
    for i in range(4):data['legal_safe_terminal_codes'][str(i+7)]='certified_flow_tube_'+str(i)
    return data
def headers(data,path):return parent.headers(data,path)
