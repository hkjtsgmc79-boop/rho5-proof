#!/usr/bin/env python3
from pathlib import Path
import copy, hashlib, json, os, shutil, tempfile
from native_campaign import compose,ROOT,OWN
if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
source=ROOT/'campaign_native';rejected=[]
with tempfile.TemporaryDirectory(prefix='b17_composition_',dir=OWN/'tmp')as folder:
    directory=Path(folder)
    for p in source.glob('task_*.json*'):shutil.copy2(p,directory/p.name)
    target=directory/'task_04.json';receipt=directory/'task_04.json.receipt.json'
    original=target.read_bytes();original_receipt=receipt.read_bytes()
    for label,mutation in (
        ('wrong_task',lambda d:d.update(task=5)),('wrong_path',lambda d:d.update(root_path='1')),
        ('wrong_model',lambda d:d.update(model_sha256='0'*64)),
        ('truncated_subtree',lambda d:d.update(nodes=d['nodes'][:-1])),
        ('wrong_split_type',lambda d:d.update(nodes=[{'kind':'S','axis':True},{'kind':'O'},{'kind':'O'}])),
    ):
        changed=json.loads(original);mutation(changed);target.write_text(json.dumps(changed))
        try:compose(directory,directory/'test_root.json')
        except (ValueError,KeyError,AssertionError):rejected.append(label)
        else:raise AssertionError('bad composition accepted: '+label)
        target.write_bytes(original)
    for key,value in (('tree_sha256','0'*64),('open',-1),('native_identity','0'*64)):
        changed=json.loads(original_receipt);changed[key]=value;receipt.write_text(json.dumps(changed))
        try:compose(directory,directory/'test_root.json')
        except (ValueError,KeyError,AssertionError):rejected.append('receipt_'+key)
        else:raise AssertionError('bad receipt accepted: '+key)
        receipt.write_bytes(original_receipt)
    result=compose(directory,directory/'test_root.json')
    assert (directory/'test_root.json').read_bytes()==(OWN/'batch_02_accepted/B17_FULL_PARTIAL.json').read_bytes()
out={'status':'B17_COMPOSITION_BINDING_NEGATIVE_CONTROLS_PASS','rejected':rejected,
     'positive_original_root_sha256':result['tree_sha256'],'new_research_credit':0,
     'scope':'Transport/receipt composition only; full frozen proof replay remains required',
     'source_sha256':hashlib.sha256((ROOT/'native_campaign.py').read_bytes()).hexdigest()}
(OWN/'COMPOSITION_CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
