#!/usr/bin/env python3
"""Task graft, wrong-owner rejection, and resumable exact-checkpoint tests.
Optional --discovery also tests numerical proposal/resumption; no global claim.
"""
import json,tempfile,copy
from pathlib import Path
from tree_protocol import empty_tree,verify_tree,verify_partition
from merge_tasks import merge
ROOT=Path(__file__).parent

def main(discovery=False):
    verify_partition()
    with tempfile.TemporaryDirectory()as td:
        d=Path(td)
        for task in range(40):(d/f'task_{task:02d}.json').write_text(json.dumps(empty_tree(task)))
        whole,stats=merge(d,allow_open=True)
        assert stats['nodes']==79 and stats['splits']==39 and stats['open']==40
        try:merge(d)
        except ValueError:pass
        else:raise AssertionError('open 40-root graft accepted as complete')
        changed=empty_tree(0);changed['task']=1;(d/'task_00.json').write_text(json.dumps(changed))
        try:merge(d,allow_open=True)
        except ValueError:pass
        else:raise AssertionError('wrong task owner accepted')
    out={'status':'V37_REFERENCE_PROTOCOL_PASS','partition_leaves':40,'empty_graft_nodes':79,'empty_graft_open':40,'wrong_owner_rejected':True,'strict_open_rejected':True,'discovery_rerun':False}
    if discovery:
        from probe import run
        with tempfile.TemporaryDirectory()as td:
            p=Path(td)/'resume.json'
            first=run(None,10,8,p);second=run(None,10,8,p)
            assert second['nodes']>=first['nodes']
            verify_tree(json.loads(p.read_text()),allow_open=True)
            old=p.read_bytes()
            try:run(1,10,8,p)
            except ValueError:pass
            else:raise AssertionError('wrong root resume accepted')
            assert p.read_bytes()==old
            out.update({'discovery_rerun':True,'first_nodes':first['nodes'],'second_nodes':second['nodes'],'resume_wrong_owner_rejected':True})
    (ROOT/'evidence/protocol_result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
if __name__=='__main__':
    import sys
    main('--discovery'in sys.argv)
