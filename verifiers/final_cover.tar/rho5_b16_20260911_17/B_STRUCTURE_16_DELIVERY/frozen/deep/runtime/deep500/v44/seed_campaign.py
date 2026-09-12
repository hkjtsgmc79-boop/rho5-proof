"""Copy only received unpaid local covers to a new resumable campaign directory."""
from pathlib import Path
import argparse,json,shutil,hashlib
ROOT=Path(__file__).resolve().parent

def main():
 a=argparse.ArgumentParser();a.add_argument('--output',type=Path,required=True);args=a.parse_args()
 entries=json.loads((ROOT/'INSERTION_INDEX.json').read_text())['parents'];unpaid=[x for x in entries if not x['complete']]
 args.output.mkdir(parents=True,exist_ok=True)
 destinations=[args.output/f'p{x["index"]}.json'for x in unpaid]+[args.output/'UNPAID_PARENTS.json']
 if any(p.exists()for p in destinations):raise ValueError('Destination already has a checkpoint; resume it instead of overwriting')
 parents=[]
 for x in unpaid:
  src=ROOT/x['certificate_file']
  if hashlib.sha256(src.read_bytes()).hexdigest()!=x['certificate_file_sha256']:raise ValueError('Source checkpoint changed')
  shutil.copy2(src,args.output/f'p{x["index"]}.json');parents.append(json.loads((ROOT/x['parent_file']).read_text()))
 (args.output/'UNPAID_PARENTS.json').write_text(json.dumps(parents,separators=(',',':'))+'\n')
 print(json.dumps({'status':'SEEDED_UNPAID_CHECKPOINTS_ONLY','parent_count':len(parents),'no_proof_credit_added':True}))
if __name__=='__main__':main()
