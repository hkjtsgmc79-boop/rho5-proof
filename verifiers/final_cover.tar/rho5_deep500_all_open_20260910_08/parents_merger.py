"""Merge fixed, disjoint old OPEN branches using their bound paid receipts.

Ordinary merging is structural and reuses existing mathematical receipts. A
requested full_check replays exactly one fully closed merged parent under the
explicit new depth-500 rule. The production root is never changed here.
"""
from pathlib import Path
from collections import Counter
import copy
import json
import os
import sys
import time
import traceback

sys.setrecursionlimit(10000)
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
from resource_capacity import apply_worker_limits
from deep_math import (DEEP_RULE, SCHEMA, atomic, at, counts, digest, file_sha,
                       load_protocol, old_open_paths, validate_branch_extension,
                       validate_legacy_binding)

ELIGIBLE = {'CLOSED', 'DEPTH500_OPEN', 'RESOURCE_PAUSED', 'COVERED_BY_PRODUCTION'}


def owned(name):
    p = (ROOT / name).resolve()
    if not p.is_relative_to(ROOT):
        raise ValueError('File outside isolated task root')
    return p


def read(path):
    return json.loads(Path(path).read_text())


def count_equal(a, b):
    return all(a.get(k, 0) == b.get(k, 0) for k in set(a) | set(b))


def extension(before, after):
    """Only old OPEN leaves may extend; all old paid cover stays present."""
    if {k: v for k, v in before.items() if k != 'tree'} != {k: v for k, v in after.items() if k != 'tree'}:
        raise ValueError('Merged envelope/profile/binding differs from anchor')
    counts(after['tree'])
    pending = [(before['tree'], after['tree'])]
    kept = Counter()
    while pending:
        a, b = pending.pop()
        t, u = a['terminal'], b['terminal']
        if t['kind'] == 'O':
            if b['waves'][:len(a['waves'])] != a['waves']:
                raise ValueError('Old OPEN wave prefix lost during merge')
            kept['old_open_roots'] += 1
            continue
        if a['waves'] != b['waves']:
            raise ValueError('Old ancestor waves changed during merge')
        if t['kind'] == 'S':
            if u.get('kind') != 'S' or u['axis'] != t['axis']:
                raise ValueError('Old split changed during merge')
            kept['old_splits'] += 1
            pending.extend([(t['left'], u['left']), (t['right'], u['right'])])
        else:
            if t != u:
                raise ValueError('Old paid terminal changed during merge')
            kept['old_paid_leaves'] += 1
    return {'status': 'STRUCTURAL_EXTENSION', 'preserved': dict(kept)}


def migration(base_path, bp, expected_parent, migration_path=None):
    """Verify the immutable file/identity chain to one already paid source tree."""
    base_path = owned(str(base_path))
    mp = owned(str(migration_path)) if migration_path else base_path.parent / 'MIGRATION.json'
    m = read(mp)
    if m['schema'] != 'LEGACY_PAID_TREE_REBOUND_DEPTH500_V1' or m['same_tree_and_profile'] is not True:
        raise ValueError('Invalid migration schema or equivalence claim')
    version = mp.parent
    def member(key):
        name = m[key]
        if Path(name).name != name:
            raise ValueError('Migration members must be version-local basenames')
        return owned(str(version / name))
    paths = {key: member(key) for key in ('legacy_certificate_file', 'source_result_file', 'base_file', 'parent_file')}
    if paths['base_file'] != base_path:
        raise ValueError('Migration is bound to another base file')
    for key, hash_key in [('legacy_certificate_file', 'legacy_certificate_file_sha256'),
                          ('source_result_file', 'source_result_file_sha256'),
                          ('base_file', 'base_file_sha256'), ('parent_file', 'parent_file_sha256')]:
        if file_sha(paths[key]) != m[hash_key]:
            raise ValueError('Migration member bytes changed: ' + key)
    parent, base = read(paths['parent_file']), read(base_path)
    legacy, paid = read(paths['legacy_certificate_file']), read(paths['source_result_file'])
    if parent != expected_parent:
        raise ValueError('Migration parent differs from anchor')
    if legacy['tree'] != base['tree'] or legacy['profile'] != base['profile']:
        raise ValueError('Migration changed tree or profile')
    light = validate_legacy_binding(parent, legacy, m['legacy_rule_identity'], bp)
    if (m['deep_rule_identity'] != bp.rule_hash() or base['rule'] != DEEP_RULE
            or any(base.get(k) != value for k, value in bp.binding(parent).items())):
        raise ValueError('Migration new rule/parent identity differs')
    exact = paid['exact_receipt']
    if (paid['certificate_sha256'] != m['legacy_certificate_file_sha256']
            or paid['parent_sha256'] != m['parent_file_sha256']
            or paid['index'] != parent['index'] or exact['index'] != parent['index']):
        raise ValueError('Paid source result identity differs')
    structural = counts(base['tree'])
    for counted in (m['source_counts'], paid['counts'], exact['counts'], light['counts']):
        if not count_equal(counted, structural):
            raise ValueError('Paid source counts differ')
    expected_status = 'OPEN' if structural.get('O', 0) else 'SAFE' if structural.get('A', 0) + structural.get('H', 0) else 'EMPTY'
    if paid['status'] != expected_status or exact['status'] != expected_status:
        raise ValueError('Paid source status differs from its tree')
    reference = {'migration_file': str(mp.relative_to(ROOT)),
                 'migration_file_sha256': file_sha(mp), 'base_file_sha256': m['base_file_sha256'],
                 'legacy_certificate_file_sha256': m['legacy_certificate_file_sha256'],
                 'source_result_file_sha256': m['source_result_file_sha256'],
                 'source_result_file': str(paths['source_result_file'].relative_to(ROOT)),
                 'source_completed_epoch': m['source_completed_epoch'],
                 'legacy_rule_identity': m['legacy_rule_identity'],
                 'deep_rule_identity': m['deep_rule_identity'],
                 'paid_source_receipt_sha256': digest(exact),
                 'mathematical_replay_performed': False}
    return base, reference


def replace_target(tree, target, subtree):
    if not target:
        return copy.deepcopy(subtree)
    parent = at(tree, target[:-1])
    parent['terminal']['left' if target[-1] == '0' else 'right'] = copy.deepcopy(subtree)
    return tree


def check_worker_result(task_state, anchor, parent, bp, expected_task_id):
    folder = owned(task_state['folder'])
    task, result = read(folder / 'TASK.json'), read(folder / 'RESULT.json')
    target = task_state['target_path']
    if (task['target_path'] != target or result['target_path'] != target
            or task['index'] != parent['index'] or result['index'] != parent['index']
            or task['task_id'] != result['task_id'] or task['task_id'] != expected_task_id
            or result['status'] != task_state['status']):
        raise ValueError('Worker task/result owner differs')
    base_path, parent_path = owned(task['base_file']), owned(task['parent_file'])
    if file_sha(base_path) != task['input_sha256'] or file_sha(parent_path) != task['parent_sha256']:
        raise ValueError('Worker input bytes changed')
    if read(parent_path) != parent:
        raise ValueError('Worker parent differs from anchor')
    base, paid_ref = migration(base_path, bp, parent, task.get('migration_file'))
    extension(anchor, base)
    final_path = folder / 'final.json'
    final_sha = file_sha(final_path)
    if (result['certificate_sha256'] != final_sha
            or result['input_sha256'] != task['input_sha256']
            or result['parent_sha256'] != task['parent_sha256']):
        raise ValueError('Worker result raw hashes differ')
    projected = read(final_path)
    structural = validate_branch_extension(base, projected, target)
    v = result['verification']
    subtree = at(projected['tree'], target)
    tc = counts(subtree)
    is_closed = tc.get('O', 0) == 0
    expected_status = 'EXACT_BRANCH_CLOSED' if is_closed else 'EXACT_BRANCH_OPEN'
    if (v['schema'] != SCHEMA or v['status'] != expected_status
            or v['closed'] != is_closed or result['closed'] != is_closed
            or (result['status'] == 'CLOSED') != is_closed
            or v['target_path'] != target or v['rule'] != DEEP_RULE
            or v['rule_identity'] != bp.rule_hash()
            or v['hash_encoding'] != 'canonical_json_utf8'
            or v['base_sha256'] != digest(base) or v['parent_sha256'] != digest(parent)
            or v['projected_sha256'] != digest(projected)
            or v['subtree_sha256'] != digest(subtree)):
        raise ValueError('New exact projection receipt binding differs')
    exact = v['exact_receipt']
    if (exact['index'] != parent['index']
            or not count_equal(exact['counts'], structural['projected_counts'])
            or not count_equal(v['target_counts'], tc)
            or not count_equal(result['target_counts'], tc)):
        raise ValueError('New exact projection receipt coverage differs')
    projected_counts = structural['projected_counts']
    status = 'OPEN' if projected_counts.get('O', 0) else 'SAFE' if projected_counts.get('A', 0) + projected_counts.get('H', 0) else 'EMPTY'
    if exact['status'] != status:
        raise ValueError('New exact projection status differs')
    row = {'target_path': target, 'task_id': task['task_id'], 'kind': 'NEW_VERIFIED_BRANCH',
           'closed': is_closed, 'target_counts': tc, 'subtree_sha256': digest(subtree),
           'result_file': str((folder / 'RESULT.json').relative_to(ROOT)),
           'result_file_sha256': file_sha(folder / 'RESULT.json'),
           'projected_file_sha256': final_sha, 'verification_sha256': digest(v),
           'input_migration': paid_ref}
    return subtree, row


def strict_check(index, folder, parent, merged, coverage, bp):
    if coverage['merged_counts'].get('O', 0):
        return {'status': 'FULL_CHECK_DEFERRED_OPEN', 'remaining_open': coverage['merged_counts']['O']}
    existing = folder / 'STRICT_DEEP500_RESULT.json'
    raw_sha = coverage['merged_file_sha256']
    if existing.exists():
        prior = read(existing)
        if prior.get('merged_file_sha256') == raw_sha and prior.get('rule_identity') == bp.rule_hash():
            if (prior.get('status') != 'STRICT_DEEP500_PARENT_ACCEPTED'
                    or prior['exact_receipt']['status'] not in ('SAFE', 'EMPTY')
                    or not count_equal(prior['exact_receipt']['counts'], coverage['merged_counts'])):
                raise ValueError('Existing strict receipt is inconsistent')
            note_strict(folder, coverage)
            return {'status': 'IDENTICAL_STRICT_DEEP500_RECEIPT_REUSED', 'receipt': prior}
    began = time.monotonic()
    receipt = bp.verify(parent, merged, allow_open=False, cross_check=True)
    if receipt['status'] not in ('SAFE', 'EMPTY') or receipt['counts'].get('O', 0):
        raise ValueError('Strict new whole-parent verification remained OPEN')
    if not count_equal(receipt['counts'], coverage['merged_counts']):
        raise ValueError('Strict merged counts differ')
    result = {'status': 'STRICT_DEEP500_PARENT_ACCEPTED', 'index': index,
              'merged_file_sha256': raw_sha, 'merged_sha256': digest(merged),
              'rule': DEEP_RULE, 'rule_identity': bp.rule_hash(), 'exact_receipt': receipt,
              'source_signature': coverage['source_signature'], 'epoch': time.time(),
              'wall_seconds': time.monotonic() - began, 'whole_root_credit': False,
              'old_frozen_rule_acceptance': False, 'production_modified': False}
    atomic(existing, result)
    note_strict(folder, coverage)
    return {'status': result['status'], 'receipt': result}


def note_strict(folder, coverage):
    updated = dict(coverage)
    updated.update(status='STRICT_DEEP500_PARENT_ACCEPTED',
                   full_mathematical_replay_performed=True,
                   strict_deep500_result_file_sha256=file_sha(folder / 'STRICT_DEEP500_RESULT.json'))
    atomic(folder / 'COVERAGE.json', updated)


def merge(index, full_check=False):
    folder = ROOT / 'parents' / str(index)
    folder.mkdir(parents=True, exist_ok=True)
    anchor_record_path = ROOT / 'anchors' / str(index) / 'ANCHOR.json'
    ar = read(anchor_record_path)
    anchor_path, parent_path = owned(ar['anchor_base_file']), owned(ar['parent_file'])
    anchor, parent = read(anchor_path), read(parent_path)
    if parent['index'] != index:
        raise ValueError('Anchor index mismatch')
    targets = old_open_paths(anchor['tree'])
    if any(q.startswith(p) for p, q in zip(sorted(targets), sorted(targets)[1:])):
        raise ValueError('Anchor targets are not prefix-free')
    target_set = set(targets)
    state = read(ROOT / 'RUN_STATE.json')
    selected, signature_rows, all_target_states = [], [], {}
    for task_id, task in sorted(state['tasks'].items()):
        if int(task['index']) != index:
            continue
        target = task['target_path']
        if target not in target_set or target in all_target_states:
            raise ValueError('Task target absent from anchor or assigned twice')
        all_target_states[target] = task['status']
        if task['status'] not in ELIGIBLE:
            continue
        row = {'task_id': task_id, 'target_path': target, 'status': task['status']}
        if task['status'] == 'COVERED_BY_PRODUCTION':
            covered = owned(task['covered_base_file'])
            mp = owned(task['covered_migration_file']) if task.get('covered_migration_file') else covered.parent / 'MIGRATION.json'
            row.update(base_file_sha256=file_sha(covered), migration_file_sha256=file_sha(mp))
        else:
            tf = owned(task['folder'])
            row.update(task_file_sha256=file_sha(tf / 'TASK.json'), result_file_sha256=file_sha(tf / 'RESULT.json'))
        signature_rows.append(row)
        selected.append((task_id, task))
    signature = digest({'schema': 'RHO5_DEEP500_PARENT_MERGE_V1', 'index': index,
                        'anchor_record_file_sha256': file_sha(anchor_record_path),
                        'anchor_file_sha256': file_sha(anchor_path), 'results': signature_rows})
    cp = folder / 'COVERAGE.json'
    bp = load_protocol(ROOT)
    if cp.exists():
        previous = read(cp)
        if previous.get('source_signature') == signature:
            if file_sha(folder / 'MERGED.json') != previous['merged_file_sha256']:
                raise ValueError('Previously merged bytes changed')
            answer = {'status': 'UNCHANGED_TARGET_RESULTS_NO_REPEAT_MERGE', 'index': index,
                      'source_signature': signature, 'coverage': previous}
            if full_check:
                answer['full_check'] = strict_check(index, folder, parent, read(folder / 'MERGED.json'), previous, bp)
            return answer
    checked_anchor, anchor_ref = migration(anchor_path, bp, parent, ar.get('migration_file'))
    if checked_anchor != anchor:
        raise ValueError('Anchor migration differs')
    merged = copy.deepcopy(anchor)
    rows = []
    for task_id, task in selected:
        target = task['target_path']
        if task['status'] == 'COVERED_BY_PRODUCTION':
            source, paid_ref = migration(owned(task['covered_base_file']), bp, parent,
                                         task.get('covered_migration_file'))
            extension(anchor, source)
            subtree = at(source['tree'], target)
            tc = counts(subtree)
            if tc.get('O', 0):
                raise ValueError('Production-covered target still contains OPEN')
            row = {'task_id': task_id, 'target_path': target, 'kind': 'COVERED_BY_PRODUCTION',
                   'closed': True, 'target_counts': tc, 'subtree_sha256': digest(subtree),
                   'input_migration': paid_ref}
        else:
            subtree, row = check_worker_result(task, anchor, parent, bp, task_id)
        merged['tree'] = replace_target(merged['tree'], target, subtree)
        rows.append(row)
    structural = extension(anchor, merged)
    merged_counts = counts(merged['tree'])
    new_closed = sorted(r['target_path'] for r in rows if r['closed'] and r['kind'] == 'NEW_VERIFIED_BRANCH')
    covered = sorted(r['target_path'] for r in rows if r['kind'] == 'COVERED_BY_PRODUCTION')
    still_open = sorted(p for p in targets if counts(at(merged['tree'], p)).get('O', 0))
    if len(new_closed) + len(covered) + len(still_open) != len(targets):
        raise ValueError('Original target accounting incomplete')
    atomic(folder / 'MERGED.json', merged)
    coverage = {'schema': 'RHO5_DEEP500_PARENT_MERGE_V1', 'index': index,
                'status': 'MERGED_PARTIAL' if merged_counts.get('O', 0) else 'MERGED_COMPLETE_PENDING_STRICT',
                'source_signature': signature, 'epoch': time.time(),
                'anchor_file': str(anchor_path.relative_to(ROOT)), 'anchor_input_migration': anchor_ref,
                'merged_file_sha256': file_sha(folder / 'MERGED.json'),
                'merged_sha256': digest(merged), 'merged_counts': merged_counts,
                'original_open_targets': len(targets), 'new_closed': len(new_closed),
                'covered_by_production': len(covered), 'still_open': len(still_open),
                'new_closed_paths': new_closed, 'covered_by_production_paths': covered,
                'still_open_paths': still_open, 'included_results': rows,
                'observed_task_states': all_target_states, 'structural_extension': structural,
                'full_mathematical_replay_performed': False, 'whole_root_credit': False,
                'old_frozen_rule_acceptance': False, 'production_modified': False}
    atomic(cp, coverage)
    answer = {'status': coverage['status'], 'index': index, 'source_signature': signature,
              'new_closed': len(new_closed), 'covered_by_production': len(covered),
              'still_open': len(still_open), 'merged_counts': merged_counts}
    if full_check:
        answer['full_check'] = strict_check(index, folder, parent, merged, coverage, bp)
    return answer


def main():
    if not 2 <= len(sys.argv) <= 3 or (len(sys.argv) == 3 and sys.argv[2] not in ('full_check', '--full-check')):
        raise SystemExit('Usage: parents_merger.py <index> [full_check]')
    index = int(sys.argv[1])
    config = read(ROOT / 'CONFIG.json')
    apply_worker_limits(config)
    started_epoch = time.time()
    try:
        result = merge(index, full_check=len(sys.argv) == 3)
        folder = ROOT / 'parents' / str(index)
        strict_path = folder / 'STRICT_DEEP500_RESULT.json'
        strict_accepted = False
        if strict_path.exists():
            strict = read(strict_path)
            strict_accepted = (strict.get('status') == 'STRICT_DEEP500_PARENT_ACCEPTED'
                               and strict.get('merged_file_sha256') == file_sha(folder / 'MERGED.json'))
        atomic(folder / 'MERGE_DONE.json',
               {'status': 'SUCCESS', 'index': index, 'started_epoch': started_epoch,
                'finished_epoch': time.time(), 'merge_status': result['status'],
                'coverage_file_sha256': file_sha(folder / 'COVERAGE.json'),
                'full_check_requested': len(sys.argv) == 3,
                'strict_accepted': strict_accepted})
        # Avoid dumping long path lists in coordinator logs.
        print(json.dumps({k: v for k, v in result.items() if k not in ('coverage', 'full_check')}, sort_keys=True), flush=True)
    except BaseException:
        atomic(ROOT / 'parents' / str(index) / 'MERGE_ERROR.json',
               {'epoch': time.time(), 'index': index, 'error': traceback.format_exc(),
                'existing_outputs_preserved': True, 'automatic_retry': False})
        raise


if __name__ == '__main__':
    main()
