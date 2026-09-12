#!/usr/bin/env python3
"""Freshly regenerate data, bind it to the shipped header, then compile in isolation."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, tempfile, time
from generate_native_data import generate
ROOT=Path(__file__).resolve().parent
def build(destination):
    if os.getpriority(os.PRIO_PROCESS,0)<10:os.setpriority(os.PRIO_PROCESS,0,10)
    destination=Path(destination).resolve();destination.parent.mkdir(parents=True,exist_ok=True)
    start=time.monotonic()
    with tempfile.TemporaryDirectory(prefix='b17_compile_') as directory:
        temporary=Path(directory);generated=generate(temporary/'b17_native_data.hpp')
        assert (temporary/'b17_native_data.hpp').read_bytes()==(ROOT/'b17_native_data.hpp').read_bytes(), 'generated frozen header differs'
        shutil.copy2(ROOT/'b17_native.cpp',temporary/'b17_native.cpp')
        process=subprocess.run(['g++','-O3','-std=c++17','-fPIC','-shared',str(temporary/'b17_native.cpp'),'-o',str(destination)],capture_output=True,text=True)
    log=destination.with_suffix('.compile.log');log.write_text(process.stdout+process.stderr)
    if process.returncode:raise RuntimeError('Native compilation failed: '+str(log))
    return {'status':'FRESH_B17_NATIVE_COMPILE_BOUND_TO_FROZEN_MODELS', 'seconds':time.monotonic()-start,
            'library':str(destination),'library_sha256':hashlib.sha256(destination.read_bytes()).hexdigest(),
            'source_sha256':hashlib.sha256((ROOT/'b17_native.cpp').read_bytes()).hexdigest(),**generated}
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,default=ROOT/'libb17_native.so');args=parser.parse_args()
    print(json.dumps(build(args.out),indent=2))
