#!/usr/bin/env python3
"""Portable exact replay. No search, no network, no third-party packages.

The complete source certificate is checked by the frozen V44/deep500 verifier.
The depth-eight anchor remains partial until both B16 source proofs arrive.
"""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, stat, subprocess, sys, tempfile, time, zipfile

ROOT=Path(__file__).resolve().parent
ARCHIVE_HASH='cc22b378fc004d0e14b4b1c5e71c76b0edc517e71884aaf95d93867eeab674b2'

def require(ok,msg):
    if not ok:raise ValueError(msg)

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()

def relative_file(name):
    p=PurePosixPath(name)
    require(not p.is_absolute() and '..'not in p.parts and '\\'not in name,'Invalid relative path')
    return ROOT.joinpath(*p.parts)

def check_manifest():
    data=json.loads((ROOT/'MANIFEST_SHA256.json').read_text(encoding='utf-8'))
    require(data['schema']=='V53_DELIVERY_MANIFEST_V1','Wrong manifest')
    for name,expected in data['files'].items():
        path=relative_file(name)
        require(path.is_file() and sha(path)==expected,'File identity mismatch: '+name)
    return len(data['files'])

def extract_input(dest):
    source=ROOT/'inputs/RHO5_REMAINING_THREE_SOURCES.zip'
    require(sha(source)==ARCHIVE_HASH,'Wrong received input archive')
    with zipfile.ZipFile(source) as z:
        infos=z.infolist();names=[x.filename for x in infos]
        require(len(names)==len(set(names)),'Duplicate ZIP names')
        require(sum(x.file_size for x in infos)<=2**30,'Unexpected expanded input size')
        for info in infos:
            p=PurePosixPath(info.filename)
            require(not p.is_absolute() and '..'not in p.parts and '\\'not in info.filename,'Unsafe ZIP path')
            require(not stat.S_ISLNK(info.external_attr>>16),'ZIP symbolic link rejected')
        require(z.testzip()is None,'Input archive CRC failure')
        z.extractall(dest)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',type=Path,default=Path.cwd()/'V53_REPLAY_RESULT.json')
    ap.add_argument('--artifacts',type=Path,default=Path.cwd()/'V53_REPLAY_ARTIFACTS')
    ap.add_argument('--source-only',action='store_true')
    ap.add_argument('--require-anchor-complete',action='store_true')
    args=ap.parse_args()
    require(__debug__,'Optimized Python is not an accepted replay mode')
    require(not(args.source_only and args.require_anchor_complete),'Source-only cannot require anchor completion')
    count=check_manifest();start=time.monotonic()
    output=args.output.resolve();artifacts=args.artifacts.resolve()
    output.parent.mkdir(parents=True,exist_ok=True);artifacts.mkdir(parents=True,exist_ok=True)
    print('V53_STATIC_FILE_IDENTITIES_PASS',count,flush=True)
    with tempfile.TemporaryDirectory(prefix='rho5_v53_replay_') as td:
        inp=Path(td)/'source';inp.mkdir();extract_input(inp)
        env=os.environ.copy();env.update(V53_INPUT=str(inp),V53_PROOF_DIR=str(ROOT/'proof'),PYTHONDONTWRITEBYTECODE='1')
        cmd=[sys.executable,'-S','-u',str(ROOT/'scripts/v53_verify.py'),'--output',str(output),'--artifacts',str(artifacts)]
        if args.source_only:cmd.append('--source-only')
        if args.require_anchor_complete:cmd.append('--require-anchor-complete')
        child=subprocess.Popen(cmd,env=env,cwd=ROOT)
        try:code=child.wait()
        except BaseException:
            child.terminate();child.wait();raise
        if code:return code
    result=json.loads(output.read_text(encoding='utf-8'))
    require(result.get('anchor_closed')is False,'Unexpected anchor closure claim')
    if args.source_only:
        require(result.get('status')=='V53_DEPTH19_ENTIRE_SOURCE_EXACT_PASS','Source replay failed')
    else:
        expected=json.loads((ROOT/'evidence/FIRST_REPLAY_RESULT.json').read_text(encoding='utf-8'))
        for k in ['status','new_complete_source_paths','new_complete_original_parents','new_C_margin',
                  'source_rebuilt_image_sha256','anchor_counts','anchor_remaining_sources',
                  'inherited_B15_conditional_waves','inherited_B15_conditional_bounds','negative_controls']:
            require(result[k]==expected[k],'Replay differs from independently checked evidence: '+k)
    result['portable_replay_seconds']=time.monotonic()-start
    result['static_files_checked']=count
    tmp=output.with_suffix(output.suffix+'.tmp');tmp.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8');tmp.replace(output)
    check_manifest()
    print('V53_PORTABLE_REPLAY_FINISHED',json.dumps({'status':result['status'],'seconds':result['portable_replay_seconds'],'source_closed':True,'anchor_closed':False,'macro_ledger':'14/15'},ensure_ascii=False),flush=True)
    return 0

if __name__=='__main__':
    try:sys.exit(main())
    except Exception as exc:
        print('V53_REPLAY_REJECTED',str(exc),file=sys.stderr,flush=True);sys.exit(2)
