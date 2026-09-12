"""Targeted ownership/grafting controls for the new parallel discovery path; X only."""
from pathlib import Path
import argparse,io,json,subprocess,tempfile
import frontier_parallel as f

def main():
    ap=argparse.ArgumentParser();ap.add_argument('task_root',type=Path);a=ap.parse_args()
    root=a.task_root.resolve();work=root/'working';tests=[]
    with tempfile.TemporaryDirectory(dir=root/'tmp',prefix='frontier_controls_') as tmp:
        tmp=Path(tmp)
        def reject(name,blob,steps):
            p=tmp/(name+'.tree');p.write_bytes(blob)
            try:f.copy_focused_payload(p,steps,io.BytesIO())
            except ValueError:tests.append(name)
            else:raise AssertionError('Malformed envelope accepted: '+name)
        for steps in ([],[(0,0)],[(3,1)],[(4,0),(10,1),(7,0)]):
            payload=b'S 1\nO\nO\n';p=tmp/'positive.tree';p.write_bytes(f.envelope(steps,payload));out=io.BytesIO()
            f.copy_focused_payload(p,steps,out);assert out.getvalue()==payload;tests.append('exact_envelope_roundtrip_'+str(len(tests)))
        steps=[(0,0),(1,1)]
        reject('wrong_ancestor',b'S 2\nO\nO\n',steps)
        reject('missing_right_sibling',b'S 0\nS 1\nO\nO\n',steps)
        reject('paid_nonowned_sibling',b'S 0\nS 1\nR 0\nO\nO\n',steps)
        reject('trailing_records',f.envelope(steps)+b'O\n',steps)
        reject('unterminated_record',f.envelope(steps)[:-1],steps)
        reject('unknown_record',f.envelope(steps,b'PASS\n'),steps)
        for name in f.PINS:
            d=work/'models'/name;data=json.loads((d/'model.json').read_text());tree=d/'checkpoint.tree'
            front=f.collect_frontiers(tree,data,name);original=f.run_verify(d/'verify',tree)
            assert len(front)==original['open'];tests.append(name+'_frontier_count_matches_exact_acceptor')
            # Identical O replacements reproduce every byte of the actual root.
            out=io.BytesIO()
            with tree.open('rb') as stream:f.copy_subtree(stream,out,lambda p,o:o.write(b'O\n'))
            assert out.getvalue()==tree.read_bytes();tests.append(name+'_original_root_identity_graft')
            e=min(front,key=lambda z:len(z['steps']));jobdir=tmp/name;jobdir.mkdir()
            job={**e,'focus':f.key(e['steps']),'directory':str(jobdir),'rounds':0,'model_sha256':f.PINS[name]}
            (jobdir/'checkpoint.tree').write_bytes(f.envelope(e['steps']))
            info=f.job_chunk(job,work,2)
            assert info['target_open']>=0 and info['open']==len(e['steps'])+info['target_open']
            tests.append(name+'_actual_focused_chunk_original_acceptor_pass')
            malformed=subprocess.run([str(d/'discover_focus'),str(jobdir/'checkpoint.tree'),str(jobdir/'invalid.tree'),'0','1','2'],capture_output=True,text=True)
            assert malformed.returncode!=0;tests.append(name+'_invalid_focus_rejected')
    out={'status':'R45_PARALLEL_FRONTIER_OWNERSHIP_AND_GRAFT_CONTROLS_PASS','checks':tests,'count':len(tests),
         'full_height_credit':False,'exact_acceptor_changed':False}
    f.write_json(root/'parallel/PARALLEL_CONTROLS.json',out);print(json.dumps(out),flush=True)

if __name__=='__main__':main()
