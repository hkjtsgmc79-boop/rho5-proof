"""Versioned depth-500 proof support; original V44 sources stay untouched.

Hashes named *_sha256 below are canonical JSON object hashes unless explicitly
named *_file_sha256. An accepted projected tree closes only its owned old OPEN.
"""
from pathlib import Path
from collections import Counter
import copy
import difflib
import hashlib
import importlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

sys.setrecursionlimit(10000)
MAX_DEPTH = 500
OLD_RULE = 'V44_POST_U41_FULL_IMAGE_BISECTION_V1'
DEEP_RULE = 'V44_POST_U41_FULL_IMAGE_BISECTION_DEPTH500_V1'
SCHEMA = 'RHO5_DEEP500_OWNED_OPEN_REPLAY_V1'
_LOADED_PINS = {}


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()


def digest(value):
    return hashlib.sha256(encoded(value)).hexdigest()


def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1048576), b''):
            h.update(chunk)
    return h.hexdigest()


def atomic(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = encoded(value) + b'\n'
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=path.name + '.', suffix='.tmp')
    try:
        with os.fdopen(fd, 'wb') as f:
            f.write(payload)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


def _source_files(folder):
    folder = Path(folder).resolve()
    return {str(p.relative_to(folder)): file_sha(p) for p in sorted(folder.rglob('*'))
            if p.is_file() and p.suffix in ('.py', '.json', '.zip')
            and '__pycache__' not in p.parts}


def build_runtime(root, legacy_v44):
    """Copy frozen package; change exactly rule name and depth acceptance limit."""
    root = Path(root).resolve()
    legacy_v44 = Path(legacy_v44).resolve()
    dest = root / 'runtime' / 'deep500' / 'v44'
    if dest.exists():
        raise ValueError('Refuse overwriting a deep runtime')
    source_files = _source_files(legacy_v44)
    if 'branch_protocol.py' not in source_files or 'v44_bootstrap.py' not in source_files:
        raise ValueError('Incomplete original V44 runtime')
    identity_program = ("import sys,json;sys.dont_write_bytecode=True;"
                        "sys.path.insert(0,sys.argv[1]);import branch_protocol as bp;"
                        "print(json.dumps({'rule':bp.RULE,'rule_identity':bp.rule_hash()}))")
    checked = subprocess.run([sys.executable, '-S', '-c', identity_program, str(legacy_v44)],
                             check=True, capture_output=True, text=True, timeout=90)
    legacy_identity = json.loads(checked.stdout)
    if legacy_identity['rule'] != OLD_RULE:
        raise ValueError('Wrong legacy rule identity')
    old = (legacy_v44 / 'branch_protocol.py').read_text()
    old_rule_line = "RULE='" + OLD_RULE + "'"
    if old.count(old_rule_line) != 1 or old.count('if depth>128:') != 1:
        raise ValueError('Unexpected original verifier source; no blind patch')
    new = old.replace(old_rule_line, "RULE='" + DEEP_RULE + "'", 1)
    new = new.replace('if depth>128:', 'if depth>500:', 1)
    compile(new, str(dest / 'branch_protocol.py'), 'exec')
    for name in source_files:
        target = dest / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(legacy_v44 / name, target)
    (dest / 'branch_protocol.py').write_text(new)
    deep_files = _source_files(dest)
    changed = [name for name in source_files if source_files[name] != deep_files[name]]
    if changed != ['branch_protocol.py'] or set(source_files) != set(deep_files):
        raise ValueError('Unexpected frozen dependency change')
    patch = ''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                                       fromfile='legacy/branch_protocol.py',
                                       tofile='deep500/branch_protocol.py'))
    diff_path = root / 'runtime' / 'DEEP500_PROTOCOL.diff'
    diff_path.write_text(patch)
    manifest = {'schema': SCHEMA, 'old_rule': OLD_RULE, 'deep_rule': DEEP_RULE,
                'legacy_rule_identity': legacy_identity['rule_identity'],
                'max_depth': MAX_DEPTH, 'legacy_runtime': str(legacy_v44),
                'deep_runtime': str(dest), 'legacy_source_sha256': digest(source_files),
                'deep_source_sha256': digest(deep_files), 'legacy_files': source_files,
                'deep_files': deep_files, 'changed_files': changed,
                'diff_file_sha256': file_sha(diff_path),
                'acceptance_resource_limit_changed': True,
                'arithmetic_and_terminal_checks_byte_preserved': True,
                'deep_entrypoint': 'deep_math.load_protocol (sets recursion limit before JSON input)',
                'epoch': time.time()}
    atomic(root / 'runtime' / 'DEEP500_MANIFEST.json', manifest)
    return manifest


def load_protocol(root):
    """Import only the task's new runtime; reject prior legacy module pollution."""
    sys.setrecursionlimit(10000)
    root = Path(root).resolve()
    v44 = root / 'runtime' / 'deep500' / 'v44'
    frozen = v44 / 'frozen' / 'v41'
    for name, folder in [('branch_protocol', v44), ('v44_bootstrap', v44),
                         ('dual_box', frozen), ('source_access', frozen),
                         ('v41_protocol', frozen)]:
        module = sys.modules.get(name)
        if module is not None and Path(module.__file__).resolve().parent != folder:
            raise ImportError('Mixed legacy/deep runtime import: ' + name)
    sys.path.insert(0, str(v44))
    bp = importlib.import_module('branch_protocol')
    boot = importlib.import_module('v44_bootstrap')
    if (Path(bp.__file__).resolve() != v44 / 'branch_protocol.py'
            or Path(bp.ROOT).resolve() != v44
            or Path(boot.__file__).resolve() != v44 / 'v44_bootstrap.py'
            or bp.RULE != DEEP_RULE):
        raise ImportError('Wrong depth-500 verifier identity/path')
    if str(v44) not in _LOADED_PINS:
        manifest = json.loads((root / 'runtime' / 'DEEP500_MANIFEST.json').read_text())
        # Full-package integrity is checked once per worker import, never per node.
        if _source_files(v44) != manifest['deep_files']:
            raise ValueError('Deep runtime source bytes changed')
        _LOADED_PINS[str(v44)] = manifest['deep_source_sha256']
    return bp


def validate_legacy_binding(parent, certificate, legacy_rule_identity, bp):
    """Lightweight identity check only; requires separately paid input receipt."""
    expect = dict(bp.binding(parent))
    expect['rule'] = OLD_RULE
    expect['rule_identity'] = legacy_rule_identity
    if not isinstance(certificate, dict) or set(certificate) != set(expect) | {'profile', 'tree'}:
        raise ValueError('Malformed original V44 envelope')
    if any(certificate[k] != value for k, value in expect.items()):
        raise ValueError('Wrong original V44 parent/source binding')
    bp.db.validate_profile(certificate['profile'])
    structure = counts(certificate['tree'])
    if structure['maxdepth'] > 128:
        raise ValueError('Original V44 input exceeds original verifier limit')
    return {'status': 'LEGACY_BINDING_AND_STRUCTURE_MATCH', 'counts': structure,
            'parent_sha256': digest(parent), 'certificate_sha256': digest(certificate),
            'legacy_rule_identity': legacy_rule_identity, 'mathematical_replay_performed': False}


def _path(path):
    if not isinstance(path, str) or len(path) > MAX_DEPTH or any(c not in '01' for c in path):
        raise ValueError('Invalid owned path')


def counts(tree):
    """Strict structure gate; mathematical wave/dual checks remain in bp.verify."""
    c = Counter()
    pending = [(tree, 0)]
    seen = set()
    while pending:
        node, depth = pending.pop()
        if depth > MAX_DEPTH:
            raise ValueError('Excessive proof depth')
        if not isinstance(node, dict) or set(node) != {'waves', 'terminal'}:
            raise ValueError('Bad branch node')
        # Cycles and shared mutable node aliases are not JSON trees.
        if id(node) in seen:
            raise ValueError('Repeated branch node object')
        seen.add(id(node))
        waves = node['waves']
        if not isinstance(waves, list) or len(waves) > 128:
            raise ValueError('Bad node wave list')
        if any(not isinstance(w, list) or not 1 <= len(w) <= 48 for w in waves):
            raise ValueError('Bad bound wave')
        c['nodes'] += 1
        c['maxdepth'] = max(c['maxdepth'], depth)
        c['new_waves'] += len(waves)
        c['new_bounds'] += sum(map(len, waves))
        terminal = node['terminal']
        if not isinstance(terminal, dict):
            raise ValueError('Missing terminal')
        kind = terminal.get('kind')
        if kind == 'S':
            if set(terminal) != {'kind', 'axis', 'left', 'right'}:
                raise ValueError('Incomplete bisection')
            if type(terminal['axis']) is not int or not 0 <= terminal['axis'] < 24:
                raise ValueError('Invalid split axis')
            pending.extend([(terminal['right'], depth + 1), (terminal['left'], depth + 1)])
        elif kind in ('I', 'O', 'A'):
            if set(terminal) != {'kind'}:
                raise ValueError('Bad simple terminal')
        elif kind not in ('C', 'H'):
            raise ValueError('Unknown terminal')
        c[kind] += 1
    if c['nodes'] != 2 * c['S'] + 1 or sum(c[k] for k in ('I', 'O', 'A', 'C', 'H')) != c['S'] + 1:
        raise ValueError('Incomplete binary cover')
    return dict(c)


def at(tree, path):
    _path(path)
    node = tree
    for bit in path:
        if node['terminal']['kind'] != 'S':
            raise ValueError('Owned path does not exist')
        node = node['terminal']['left' if bit == '0' else 'right']
    return node


def old_open_paths(tree):
    counts(tree)
    answer = []
    pending = [(tree, '')]
    while pending:
        node, path = pending.pop()
        t = node['terminal']
        if t['kind'] == 'O':
            answer.append(path)
        elif t['kind'] == 'S':
            pending.extend([(t['right'], path + '1'), (t['left'], path + '0')])
    return answer


def _open():
    return {'waves': [], 'terminal': {'kind': 'O'}}


def project(tree, target):
    """Own target subtree plus exact ancestors; all exterior siblings are O."""
    _path(target)
    at(tree, target)
    def walk(node, pos):
        if pos == len(target):
            return copy.deepcopy(node)
        t = node['terminal']
        owned = 'left' if target[pos] == '0' else 'right'
        other = 'right' if owned == 'left' else 'left'
        return {'waves': copy.deepcopy(node['waves']),
                'terminal': {'kind': 'S', 'axis': t['axis'],
                             owned: walk(t[owned], pos + 1), other: _open()}}
    result = walk(tree, 0)
    counts(result)
    return result


def validate_branch_extension(base, projected, target):
    """Check ownership and preservation independently of mathematical replay."""
    _path(target)
    if {k: v for k, v in base.items() if k != 'tree'} != {k: v for k, v in projected.items() if k != 'tree'}:
        raise ValueError('Base envelope/profile/binding changed')
    output_counts = counts(projected['tree'])
    old = at(base['tree'], target)
    initial_target_counts = counts(old)
    if not initial_target_counts.get('O', 0):
        raise ValueError('Latest target already paid; reuse its existing receipt')
    a, b = base['tree'], projected['tree']
    for bit in target:
        if a['waves'] != b['waves']:
            raise ValueError('Original ancestor wave changed')
        ta, tb = a['terminal'], b['terminal']
        if tb.get('kind') != 'S' or ta['axis'] != tb['axis']:
            raise ValueError('Original ancestor split changed')
        owned = 'left' if bit == '0' else 'right'
        other = 'right' if owned == 'left' else 'left'
        if tb[other] != _open():
            raise ValueError('Exterior sibling is not canonical OPEN')
        a, b = ta[owned], tb[owned]
    preserved = Counter()
    pending = [(a, b)]
    while pending:
        before, after = pending.pop()
        old_terminal, new_terminal = before['terminal'], after['terminal']
        if old_terminal['kind'] == 'O':
            if after['waves'][:len(before['waves'])] != before['waves']:
                raise ValueError('Original OPEN wave prefix lost')
            preserved['old_open_roots'] += 1
            continue
        if before['waves'] != after['waves']:
            raise ValueError('Existing target ancestor waves changed')
        if old_terminal['kind'] == 'S':
            if new_terminal.get('kind') != 'S' or new_terminal['axis'] != old_terminal['axis']:
                raise ValueError('Existing target split changed')
            preserved['old_splits'] += 1
            pending.extend([(old_terminal['left'], new_terminal['left']),
                            (old_terminal['right'], new_terminal['right'])])
        else:
            if old_terminal != new_terminal:
                raise ValueError('Existing target paid terminal changed')
            preserved['old_paid_leaves'] += 1
    return {'status': 'OWNED_OPEN_STRUCTURAL_EXTENSION', 'target_path': target,
            'preserved_ancestors': len(target), 'preserved_open_waves': len(a['waves']),
            'preserved_target': dict(preserved), 'initial_target_counts': initial_target_counts,
            'projected_counts': output_counts, 'target_counts': counts(b)}


def verify_branch(root, parent, deep_base, projected, target):
    """One exact owned projection replay, with complete ancestor reconstruction."""
    audit = validate_branch_extension(deep_base, projected, target)
    bp = load_protocol(root)
    if {k: deep_base.get(k) for k in bp.binding(parent)} != bp.binding(parent):
        raise ValueError('Deep base is bound to a different parent or verifier')
    start = time.monotonic()
    receipt = bp.verify(parent, projected, allow_open=True, cross_check=True)
    if receipt['counts'] != audit['projected_counts']:
        raise ValueError('Exact/structural projected count disagreement')
    target_tree = at(projected['tree'], target)
    target_counts = audit['target_counts']
    closed = target_counts.get('O', 0) == 0
    return {'schema': SCHEMA, 'status': 'EXACT_BRANCH_CLOSED' if closed else 'EXACT_BRANCH_OPEN',
            'closed': closed, 'target_path': target, 'parent_sha256': digest(parent),
            'base_sha256': digest(deep_base), 'projected_sha256': digest(projected),
            'subtree_sha256': digest(target_tree), 'hash_encoding': 'canonical_json_utf8',
            'rule': bp.RULE, 'rule_identity': bp.rule_hash(), 'exact_receipt': receipt,
            'target_counts': target_counts, 'structural_audit': audit,
            'verified_epoch': time.time(), 'verification_wall_seconds': time.monotonic() - start,
            'old_whole_tree_replayed': False, 'whole_parent_credit': False,
            'old_frozen_rule_acceptance': False}
