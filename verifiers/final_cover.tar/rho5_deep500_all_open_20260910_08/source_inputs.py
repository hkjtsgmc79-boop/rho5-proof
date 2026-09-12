"""Immutable, paid completed input snapshots. No historical mathematical replay."""
from pathlib import Path
import copy
import json
import shutil
import sys
import time
sys.setrecursionlimit(10000)
import deep_math as dm
from fast_checkpoint import atomic_json


def read(path):
    return json.loads(Path(path).read_text())


def same_counts(a, b):
    return all(a.get(k, 0) == b.get(k, 0) for k in set(a) | set(b))


def extension(old, new):
    if {k: v for k, v in old.items() if k != 'tree'} != {k: v for k, v in new.items() if k != 'tree'}:
        raise ValueError('Certificate envelope changed')
    pending = [(old['tree'], new['tree'])]
    while pending:
        a, b = pending.pop()
        if a['terminal']['kind'] == 'O':
            if b['waves'][:len(a['waves'])] != a['waves']:
                raise ValueError('Original OPEN waves lost')
            continue
        if a['waves'] != b['waves']:
            raise ValueError('Original ancestor waves changed')
        ta, tb = a['terminal'], b['terminal']
        if ta['kind'] == 'S':
            if tb.get('kind') != 'S' or ta['axis'] != tb['axis']:
                raise ValueError('Original split changed')
            pending.extend([(ta['left'], tb['left']), (ta['right'], tb['right'])])
        elif ta != tb:
            raise ValueError('Original paid leaf changed')
    return True


class Inputs:
    def __init__(self, root, config):
        self.root = Path(root).resolve()
        self.config = config
        self.source = Path(config['source_root']).resolve()
        manifest_path = self.root / 'runtime/DEEP500_MANIFEST.json'
        if not manifest_path.exists():
            manifest = dm.build_runtime(self.root, self.source / 'runtime/v44')
        else:
            manifest = read(manifest_path)
        if manifest['legacy_source_sha256'] != config['source_pin']:
            raise ValueError('Pinned original source mismatch')
        self.manifest = manifest
        self.bp = dm.load_protocol(root)
        self.rule_identity = self.bp.rule_hash()
        self.cache = {}

    def source_path(self, name):
        p = (self.source / name).resolve()
        if not p.is_relative_to(self.source):
            raise ValueError('Source path escaped authorized project')
        return p

    def rows(self):
        return read(self.source / 'STATE.json')['cases']

    def snapshot(self, row):
        index = int(row['index'])
        key = (index, row['certificate_sha256'])
        if key in self.cache:
            return self.cache[key]
        dest = self.root / 'versions' / str(index) / row['certificate_sha256']
        migration = dest / 'MIGRATION.json'
        if not migration.exists():
            parent_path, cert_path = self.source_path(row['parent']), self.source_path(row['certificate'])
            result_path = self.source_path(row['last_result'])
            if dm.file_sha(parent_path) != row['parent_sha256'] or dm.file_sha(cert_path) != row['certificate_sha256']:
                raise ValueError('Completed input byte hash mismatch')
            parent, old, result = read(parent_path), read(cert_path), read(result_path)
            if parent['index'] != index or result['index'] != index:
                raise ValueError('Completed receipt wrong index')
            if result['certificate_sha256'] != row['certificate_sha256'] or result['parent_sha256'] != row['parent_sha256']:
                raise ValueError('Completed receipt wrong certificate/parent')
            if result['status'] not in ('OPEN', 'SAFE', 'EMPTY', 'CLOSED'):
                raise ValueError('Completed result was not accepted')
            check = dm.validate_legacy_binding(parent, old, self.manifest['legacy_rule_identity'], self.bp)
            c = check['counts']
            if not all(same_counts(c, x) for x in (row['counts'], result['counts'], result['exact_receipt']['counts'])):
                raise ValueError('Completed exact receipt count mismatch')
            if result['exact_receipt']['index'] != index or result['exact_receipt']['status'] not in ('OPEN', 'SAFE', 'EMPTY'):
                raise ValueError('Missing completed mathematical receipt')
            expected = 'OPEN' if c.get('O', 0) else 'SAFE' if c.get('A', 0) or c.get('H', 0) else 'EMPTY'
            if result['status'] != expected or result['exact_receipt']['status'] != expected or result['complete'] != (not c.get('O', 0)):
                raise ValueError('Completed receipt status/coverage mismatch')
            base = self.bp.wrap(parent, copy.deepcopy(old['tree']), old['profile'])
            dest.mkdir(parents=True, exist_ok=True)
            for src, name in ((parent_path, 'parent.json'), (cert_path, 'legacy.json'), (result_path, 'SOURCE_RESULT.json')):
                shutil.copyfile(src, dest / name)
            atomic_json(dest / 'base.json', base)
            m = {'schema': 'LEGACY_PAID_TREE_REBOUND_DEPTH500_V1',
                 'index': index, 'legacy_certificate_file_sha256': row['certificate_sha256'],
                 'parent_file_sha256': row['parent_sha256'], 'base_file_sha256': dm.file_sha(dest / 'base.json'),
                 'source_result_file_sha256': dm.file_sha(dest / 'SOURCE_RESULT.json'),
                 'legacy_rule_identity': self.manifest['legacy_rule_identity'], 'deep_rule_identity': self.rule_identity,
                 'legacy_certificate_file': 'legacy.json', 'source_result_file': 'SOURCE_RESULT.json',
                 'base_file': 'base.json', 'parent_file': 'parent.json', 'same_tree_and_profile': True,
                 'legacy_binding_check': check, 'source_counts': result['counts'],
                 'source_completed_epoch': row.get('completed_epoch', result.get('finished_epoch')),
                 'source_root': str(self.source), 'source_certificate': row['certificate'],
                 'source_result': row['last_result'], 'created_epoch': time.time(),
                 'old_mathematical_replay_performed': False, 'new_math_receipt_claimed': False}
            atomic_json(migration, m)
        m = read(migration)
        if m['index'] != index or m['legacy_rule_identity'] != self.manifest['legacy_rule_identity'] or m['deep_rule_identity'] != self.rule_identity:
            raise ValueError('Saved migration runtime identity mismatch')
        for name, field in [('parent.json', 'parent_file_sha256'), ('legacy.json', 'legacy_certificate_file_sha256'),
                            ('base.json', 'base_file_sha256'), ('SOURCE_RESULT.json', 'source_result_file_sha256')]:
            if dm.file_sha(dest / name) != m[field]:
                raise ValueError('Saved snapshot changed: ' + name)
        if m['legacy_certificate_file_sha256'] != row['certificate_sha256'] or m['parent_file_sha256'] != row['parent_sha256']:
            raise ValueError('Snapshot does not match requested input')
        value = {'folder': str(dest.relative_to(self.root)), 'migration': m,
                 'legacy': read(dest / 'legacy.json'), 'base': read(dest / 'base.json')}
        # Certificates can be large. Keep only the current and anchor versions in coordinator state on disk.
        self.cache[key] = value
        for previous in [k for k in self.cache if k[0] == index and k != key]:
            del self.cache[previous]
        return value

    def anchor(self, row):
        p = self.root / 'anchors' / str(row['index']) / 'ANCHOR.json'
        if p.exists():
            return read(p)
        version = self.snapshot(row)
        folder = version['folder']
        a = {'index': int(row['index']), 'anchor_base_file': folder + '/base.json',
             'anchor_legacy_file': folder + '/legacy.json', 'parent_file': folder + '/parent.json',
             'migration_file': folder + '/MIGRATION.json', 'original_open_paths': dm.old_open_paths(version['base']['tree']),
             'created_epoch': time.time(), 'source_certificate_sha256': row['certificate_sha256']}
        p.parent.mkdir(parents=True, exist_ok=True)
        atomic_json(p, a)
        return a

    def latest_for(self, index, anchor):
        row = self.rows()[str(index)]
        version = self.snapshot(row)
        old = read(self.root / anchor['anchor_legacy_file'])
        extension(old, version['legacy'])
        return row, version


if __name__ == '__main__':
    root = Path(__file__).resolve().parent
    inputs = Inputs(root, read(root / 'CONFIG.json'))
    print(json.dumps({'status': 'RUNTIME_READY', 'deep_rule_identity': inputs.rule_identity,
                      'legacy_source_sha256': inputs.manifest['legacy_source_sha256']}))
