from pathlib import Path
import argparse,json
from _v42_bootstrap import v41_api
import bound_protocol as bp
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('box');ap.add_argument('certificate');ap.add_argument('--allow-open',action='store_true');a=ap.parse_args()
 b=json.loads(Path(a.box).read_text());b=b['box']if isinstance(b,dict)else b;n=json.loads(Path(a.certificate).read_text())
 try:
  if n.get('kind')in('U41','G41'):r=v41_api()[0].verify(b,n,a.allow_open,cross_check=True)
  else:r=bp.verify(b,n,a.allow_open,cross_check=True)
 except Exception as e:print(json.dumps({'status':'REJECTED','error':str(e)}));raise SystemExit(2)
 print(json.dumps(r,indent=2))
