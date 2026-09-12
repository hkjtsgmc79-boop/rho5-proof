#!/usr/bin/env python3
"""Download fixed release assets, verify SHA-256, and reassemble transport parts.

This checks file identity only. It does not verify mathematical certificates.
Uses only the Python standard library. Partial downloads can be resumed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import urllib.request

ROOT = Path(__file__).resolve().parents[1]

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(4 * 1024**2), b''):
            h.update(block)
    return h.hexdigest()

def checked(path, entry):
    return path.exists() and path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256']

def download(entry, out):
    name = entry['name']
    if Path(name).name != name:
        raise ValueError('Expected a plain asset filename')
    dest = out / name
    if checked(dest, entry):
        print('SHA256 PASS (existing):', name, flush=True)
        return dest
    if dest.exists():
        raise RuntimeError(f'{dest} exists but fails its fixed checksum; move it aside before retrying')
    partial = out / (name + '.download')
    if checked(partial, entry):
        partial.replace(dest)
        print('SHA256 PASS (completed partial):', name, flush=True)
        return dest
    offset = partial.stat().st_size if partial.exists() else 0
    if offset >= entry['bytes']:
        raise RuntimeError(f'{partial} has an invalid completed payload; move it aside before retrying')
    headers = {'User-Agent': 'rho5-proof-reproduction'}
    if offset:
        headers['Range'] = f'bytes={offset}-'
    print('Downloading:', name, '(resume bytes:', offset, ')', flush=True)
    request = urllib.request.Request(entry['url'], headers=headers)
    with urllib.request.urlopen(request, timeout=120) as response:
        resumed = offset > 0 and response.status == 206
        if resumed and not response.headers.get('Content-Range', '').startswith(f'bytes {offset}-'):
            raise RuntimeError('Server returned an unexpected range')
        with partial.open('ab' if resumed else 'wb') as f:
            shutil.copyfileobj(response, f, length=4 * 1024**2)
    if not checked(partial, entry):
        raise RuntimeError(f'Incomplete download or SHA-256 mismatch: {partial}; no verification credit')
    partial.replace(dest)
    print('SHA256 PASS:', name, flush=True)
    return dest

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--list', action='store_true')
    parser.add_argument('--group', action='append', choices=['lean', 'sample', 'x', 'b', 'upstream', 'analytic'])
    parser.add_argument('--id', action='append', help='Exact object id shown by --list')
    parser.add_argument('--all', action='store_true')
    parser.add_argument('--out', type=Path, default=ROOT / 'downloads')
    args = parser.parse_args()
    data = json.loads((ROOT / 'manifests/release-assets.json').read_text())
    objects = data['objects']
    if args.list:
        for x in objects:
            print(f"{x['id']:30s} {x['group']:10s} {x['bytes']/1e6:10.2f} MB  {x['filename']}")
        return
    if not (args.all or args.group or args.id):
        parser.error('Choose --list, --group, --id or --all; no downloads start by default')
    unknown = set(args.id or []) - {x['id'] for x in objects}
    if unknown:
        parser.error('Unknown object ids: ' + ', '.join(sorted(unknown)))
    selected = [x for x in objects if args.all or x['group'] in (args.group or []) or x['id'] in (args.id or [])]
    args.out.mkdir(parents=True, exist_ok=True)
    for obj in selected:
        target = args.out / obj['filename']
        if checked(target, obj):
            print('SHA256 PASS (whole archive):', obj['filename'], flush=True)
            continue
        parts = [download(a, args.out) for a in obj['assets']]
        if len(parts) > 1:
            if target.exists():
                raise RuntimeError(f'{target} exists with a different checksum; move it aside')
            pending = args.out / (obj['filename'] + '.assembling')
            with pending.open('wb') as f:
                for part in parts:
                    with part.open('rb') as source:
                        shutil.copyfileobj(source, f, length=4 * 1024**2)
            if not checked(pending, obj):
                raise RuntimeError('Reassembled archive checksum mismatch')
            pending.replace(target)
        if not checked(target, obj):
            raise RuntimeError('Whole archive checksum mismatch')
        print('ARCHIVE IDENTITY PASS:', obj['filename'], flush=True)
    print('Download and SHA-256 checks complete. Mathematical verification has not been run.')

if __name__ == '__main__':
    main()
