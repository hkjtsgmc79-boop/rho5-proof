#!/usr/bin/env python3
from __future__ import annotations
import json,subprocess,sys,tempfile,shutil
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def main(binary,tree):
    cases={
        'unpaid_open':'O\n','unpaid_Q':'Q\n','unknown_tag':'PASS\n',
        'split_out_of_range':'S 22\n','negative_split':'S -1\n','truncated_tree':'S 0\n',
        'empty_support':'C 0\n','zero_weight':'C 1 0 0\n','negative_weight':'C 1 0 -1\n',
        'duplicate_row':'C 2 0 1 0 2\n','bad_row':'C 1 246 1\n',
        'noncontradiction':'C 1 0 1\n','integer_overflow_input':'C 1 0 99999999999999999999999999999\n'
    }
    passed=[]
    with tempfile.TemporaryDirectory(prefix='v31_negative_') as td:
        folder=Path(td)
        for name,text in cases.items():
            path=folder/(name+'.tree');path.write_text(text,encoding='ascii')
            run=subprocess.run([binary,str(path)],capture_output=True,text=True,timeout=20)
            if run.returncode==0 or 'REJECTED:' not in run.stderr:raise AssertionError('False acceptance: '+name)
            passed.append(name)
        tail=folder/'unused_tail.tree'
        with open(tree,'rb') as src,tail.open('wb') as dst:
            shutil.copyfileobj(src,dst);dst.write(b'\nC 1 0 1\n')
        run=subprocess.run([binary,str(tail)],capture_output=True,text=True,timeout=30)
        if run.returncode==0 or 'trailing unvisited records' not in run.stderr:raise AssertionError('Unused tail accepted')
        passed.append('unused_tail')
        data=json.loads((ROOT/'mc_exact_model.json').read_text());data['rows'][0]['rhs']+=1
        bad=folder/'bad_model.json';bad.write_text(json.dumps(data))
        run=subprocess.run([sys.executable,str(ROOT/'verify_model.py'),str(bad)],capture_output=True,text=True,timeout=20)
        if run.returncode==0 or 'symbolic source/JSON mismatch' not in run.stderr:raise AssertionError('Mutated model accepted')
        passed.append('wrong_model_coefficient')
    print(json.dumps(dict(status='V31_NEGATIVE_CONTROLS_PASS',correctly_rejected=len(passed),cases=passed)))
if __name__=='__main__':main(sys.argv[1],sys.argv[2])
