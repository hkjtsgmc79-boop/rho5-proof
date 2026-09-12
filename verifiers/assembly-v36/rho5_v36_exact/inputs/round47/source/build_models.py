from pathlib import Path
import json,hashlib
import build_models_flow_parent as parent
ROOT=Path(__file__).resolve().parent
EXPECTED_RULE={'schema': 'rho5.exact.weighted-height.v1', 'terminal': 'H t n row_1 w_1 ... row_n w_n', 'objective': 'F=r-w', 'alpha_definition_sha256': '9af09b9d6e584bba2a7cef7e9e3993f128fbc90744335eb0c22c8b11e0226959', 'weights': 'distinct original physical/McCormick row indices; positive signed-64-bit integer weights', 't': 'positive signed-64-bit integer', 'acceptance': 'B-min_box((sum(weights*rows)-t*F)) <= t*alpha_lower', 'box': 'the original exact ancestral box, with outward corner bounds for each lifted product', 'scope': 'every original physical source in that box; gamma remains a localization trigger', 'arithmetic': 'all final acceptance uses unbounded integers; numerical duals are proposals only', 'classification': 'alpha safety, never a contradiction; original C/R/P and A0..10 unchanged'}
def make_model(K,J,typ,branch='low'):
 data=parent.make_model(K,J,typ,branch)
 p=ROOT/'reference/flow_tube_parent_models'/f'{typ}_LOW_ALPHA.json'
 if data!=json.loads(p.read_text()):raise ValueError('Flow-tube semantic parent changed')
 rule=json.loads((ROOT/'WEIGHTED_HEIGHT_RULE.json').read_text())
 if rule!=EXPECTED_RULE:raise ValueError('Weighted height rule changed')
 if rule['alpha_definition_sha256']!=hashlib.sha256((ROOT/'alpha.json').read_bytes()).hexdigest():raise ValueError('Weighted height alpha binding changed')
 data['source_version']='V35_CQG_ROUND47_WEIGHTED_HEIGHT_2026-09-08'
 data['previous_version_model_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
 data['weighted_height_rule_sha256']=hashlib.sha256((ROOT/'WEIGHTED_HEIGHT_RULE.json').read_bytes()).hexdigest()
 data['legal_safe_terminal_codes']['H']='exact_positive_weighted_height_upper_bound'
 return data
def headers(data,path):return parent.headers(data,path)
