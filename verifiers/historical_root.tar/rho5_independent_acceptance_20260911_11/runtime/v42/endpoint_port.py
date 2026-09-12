"""Read-only small-batch point of entry for a complete supplied U41 partial record.
Never modifies the user's original tree. OPEN remains OPEN.
"""
from pathlib import Path
import argparse,json
import bound_protocol as bp
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('source_record');ap.add_argument('--output',required=True);ap.add_argument('--literal',action='store_true');a=ap.parse_args()
 s=json.loads(Path(a.source_record).read_text());box=s['box'];prefix=s['partial_certificate']
 node=bp.wrap(box,prefix,'B42',method='one_slack',symmetries=not a.literal)
 result=bp.verify(box,node,allow_open=True,cross_check=True)
 out=Path(a.output);out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(node)+'\n')
 out.with_suffix(out.suffix+'.receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'certificate':str(out),'original_tree_modified':False}))
