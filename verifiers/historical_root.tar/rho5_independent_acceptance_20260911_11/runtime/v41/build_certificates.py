"""Package previously discovered exact traces. Does not search or assert success.
The imported source evidence records floats only as discovery timing metadata;
mathematical traces contain integer weights and exact boxes.
"""
from pathlib import Path
import json,gzip
from source_access import ROOT,SOURCE
from v41_protocol import wrap

def run():
    records=json.loads((ROOT/'evidence/selected_traces.json').read_text())
    samples=json.loads((SOURCE/'REMAINING_SAMPLES64.json').read_text())
    index=[]
    for n,item in enumerate(samples):
        entry=records[str(n)];trace=entry['trace'];box=item['box']
        dst=ROOT/'certificates'/f'sample_{n:02d}.json';dst.parent.mkdir(exist_ok=True)
        dst.write_text(json.dumps(wrap(box,trace),sort_keys=True,separators=(',',':'))+'\n')
        bp=ROOT/'controls'/f'sample_{n:02d}_box.json';bp.write_text(json.dumps(box)+'\n')
        index.append(dict(sample_ordinal=n,reported_original_index=item['index'],reported_path=item['path'],
          box=box,box_sha256=item['box_sha256'],certificate=str(dst.relative_to(ROOT)),
          proposed_status='OPEN'if trace['terminal']['kind']=='O'else 'EMPTY',
          profile=trace['profile'],waves=len(trace['waves']),bounds=sum(map(len,trace['waves'])),
          full_original_tree_received=False,ancestry_requires_controller_check=True))
    (ROOT/'INSERTION_INDEX.json').write_text(json.dumps(index,ensure_ascii=False,indent=2)+'\n')
    return index
if __name__=='__main__':print(json.dumps(dict(packaged=len(run()))))
