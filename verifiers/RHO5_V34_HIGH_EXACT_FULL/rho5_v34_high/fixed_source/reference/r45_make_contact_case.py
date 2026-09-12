#!/usr/bin/env python3
"""Create ONE static member of the proved 50-case endpoint cover.
No existing checkpoint may be attached to the new model without full rechecking.
Example: python make_contact_case.py --type II --case-id 19 --out models/II_case19
"""
from pathlib import Path
from copy import deepcopy
import argparse,json,shutil,hashlib
import sympy as s
from build_model import make_model,headers

def contact_cases():
    rows=['S01-','O01-','S02+','S02-','O02+','O02-']
    cols=[f'{layer}{i}0{sig}'for i in (1,2)for layer in ('S','O')for sig in ('+','-')]
    out=[['S00+'],['O00+']]+[[a,b]for a in rows for b in cols]
    assert len(out)==50 and len(set(map(tuple,out)))==50
    return out

def add_case(base,case_id):
    if not 0<=case_id<50:raise ValueError('case_id must be 0..49')
    data=deepcopy(base);selected=contact_cases()[case_id];lookup={r['name']:r for r in base['rows']}
    for name in selected:
        row=deepcopy(lookup[name]);row['name']='CONTACT_EQ_'+name
        row['coefficients']=[-v for v in row['coefficients']];row['rhs']=-row['rhs'];row['polynomial']=str(s.expand(-s.sympify(row['polynomial'])))
        data['rows'].append(row)
    data['contact_case']={'id':case_id,'equalities':selected,'total_cover_cases':50,'scope':'selected contact case only; not entire type'}
    return data

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--K',default='21/10');ap.add_argument('--J',default='107/50');ap.add_argument('--type',choices=['I','II'],required=True);ap.add_argument('--case-id',type=int,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    if (a.out/'model.json').exists()or (a.out/'checkpoint.tree').exists():raise ValueError('refusing to overwrite an existing frozen model/checkpoint')
    data=add_case(make_model(a.K,a.J,a.type),a.case_id);headers(data,a.out)
    print(json.dumps({'model_sha256':hashlib.sha256((a.out/'model.json').read_bytes()).hexdigest(),'case':data['contact_case'],'status':'MODEL_CREATED_NOT_SOLVED'},indent=2))
if __name__=='__main__':main()
