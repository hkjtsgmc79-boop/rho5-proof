#!/usr/bin/env python3
"""Restore byte-identical B16 frozen dependencies from the embedded old archive.
This performs file/hash checks only. It does not execute any mathematical proof.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import os
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
B16 = ROOT / 'B_STRUCTURE_16_DELIVERY'
V53 = ROOT / 'rho5_v53_exact'
ARCHIVE_SHA = 'cc22b378fc004d0e14b4b1c5e71c76b0edc517e71884aaf95d93867eeab674b2'
B16_MANIFEST_SHA = '753e63da04f7b66e396addc7afb171dbf693de2c2b1df0e205460683f1f31d38'
B16_PAYLOAD_SHA = '05ffe70f25190657b8aed50f52855f4796a322ec120a350e847ce516852206be'
V53_MANIFEST_SHA = '58831b8529e37095abeba8f9ceeb41f98245a9aab530ef2176c60662438c30df'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def path_for(root, name):
    require(type(name) is str and '\\' not in name, 'Invalid file name')
    p = PurePosixPath(name)
    require(not p.is_absolute() and '..' not in p.parts, 'Unsafe relative file name')
    target = root.joinpath(*p.parts)
    require(target.resolve().is_relative_to(root.resolve()), 'Path escapes package')
    require(not any(parent.is_symlink() for parent in [target, *target.parents]), 'Symlink input rejected')
    return target


def check_entries(root, entries):
    for name, expected in entries.items():
        p = path_for(root, name)
        require(p.is_file() and sha(p) == expected, 'File/hash mismatch: ' + str(p))


def main():
    archive = V53 / 'inputs/RHO5_REMAINING_THREE_SOURCES.zip'
    for path, expected in [(archive, ARCHIVE_SHA),
                           (B16/'MANIFEST_SHA256.json', B16_MANIFEST_SHA),
                           (B16/'PROOF_PAYLOAD_SHA256.json', B16_PAYLOAD_SHA),
                           (V53/'MANIFEST_SHA256.json', V53_MANIFEST_SHA)]:
        require(path.is_file() and sha(path) == expected, 'Changed fixed input: ' + str(path))
    outer = json.loads((B16/'MANIFEST_SHA256.json').read_text(encoding='utf-8'))
    payload = json.loads((B16/'PROOF_PAYLOAD_SHA256.json').read_text(encoding='utf-8'))
    v53 = json.loads((V53/'MANIFEST_SHA256.json').read_text(encoding='utf-8'))
    require(len(outer['files']) == 190 and len(payload['files']) == 179 and len(v53['files']) == 25,
            'Unexpected manifest cardinality')
    require(payload['schema'] == 'B16_EXACT_PAYLOAD_V1', 'Wrong B16 payload schema')
    wanted = {name: value for name, value in outer['files'].items() if name.startswith('frozen/deep/')}
    require(len(wanted) == 165, 'Unexpected shared dependency count')
    require(all(payload['files'].get(name) == value for name, value in wanted.items()),
            'Outer/payload dependency identity mismatch')
    check_entries(V53, v53['files'])
    check_entries(B16, {name: value for name,value in outer['files'].items() if name not in wanted})
    restored = 0
    already_present = 0
    with zipfile.ZipFile(archive) as z:
        names = z.namelist()
        require(len(names) == len(set(names)), 'Duplicate embedded ZIP names')
        for name, expected in sorted(wanted.items()):
            member = 'B_STRUCTURE_15/' + name
            require(member in names, 'Missing archived shared dependency: ' + member)
            blob = z.read(member)
            require(hashlib.sha256(blob).hexdigest() == expected, 'Wrong archived dependency bytes: ' + member)
            target = path_for(B16, name)
            if target.exists():
                require(target.is_file() and sha(target) == expected, 'Refuse to replace changed dependency')
                already_present += 1
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            temp = target.with_name(target.name + '.restore.tmp')
            require(not temp.exists(), 'Unfinished restore file exists: ' + str(temp))
            with temp.open('xb') as f:
                f.write(blob)
            os.replace(temp, target)
            restored += 1
    check_entries(B16, outer['files'])
    check_entries(B16, payload['files'])
    result = {'status': 'FROZEN_INPUT_RESTORATION_HASH_PASS', 'mathematical_replay': False,
              'shared_dependency_files': 165, 'restored': restored,
              'already_present': already_present, 'b16_outer_files_checked': 190,
              'b16_payload_files_checked': 179, 'v53_files_checked': 25,
              'embedded_archive_sha256': ARCHIVE_SHA}
    print(json.dumps(result, ensure_ascii=False, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
