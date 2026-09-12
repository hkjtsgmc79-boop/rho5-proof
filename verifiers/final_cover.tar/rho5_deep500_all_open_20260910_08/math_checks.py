"""Small deep-500 structural and verifier-boundary controls; no old-tree replay.

Optional --known-parent/--known-certificate checks exactly one caller-selected
small legitimate old certificate after explicit new-identity wrapping.
"""
from pathlib import Path
from fractions import Fraction
from types import SimpleNamespace
import argparse
import ast
import copy
import json
import sys

sys.setrecursionlimit(10000)
from deep_math import (MAX_DEPTH, DEEP_RULE, OLD_RULE, counts, project,
                       validate_branch_extension, load_protocol, digest, atomic)


def leaf(kind='O', waves=None):
    return {'waves': [] if waves is None else waves, 'terminal': {'kind': kind}}


def chain(depth):
    node = leaf()
    for _ in range(depth):
        node = {'waves': [], 'terminal': {'kind': 'S', 'axis': 0,
                                        'left': node, 'right': leaf()}}
    return node


def small_controls(root):
    root = Path(root).resolve()
    passed = []
    def rejects(name, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError):
            passed.append(name)
        else:
            raise AssertionError('Negative control accepted: ' + name)
    bp = load_protocol(root)
    manifest = json.loads((root / 'runtime' / 'DEEP500_MANIFEST.json').read_text())
    assert bp.RULE == DEEP_RULE != OLD_RULE
    assert bp.rule_hash() != manifest['legacy_rule_identity']
    assert manifest['legacy_files']['branch_protocol.py'] != manifest['deep_files']['branch_protocol.py']
    passed.append('explicit_new_rule_and_source_identity')
    deep = chain(MAX_DEPTH)
    roundtrip = json.loads(json.dumps(deep, sort_keys=True, separators=(',', ':')))
    assert roundtrip == deep and copy.deepcopy(roundtrip) == deep
    assert counts(roundtrip)['maxdepth'] == MAX_DEPTH
    passed.append('depth500_json_deepcopy_roundtrip')
    rejects('depth501_structure_rejected', lambda: counts(chain(MAX_DEPTH + 1)))
    wave = [[{'fixture': 'old_bound'}]]
    base = {'rule': DEEP_RULE, 'profile': 'PIVOT_CYCLE', 'tree':
            {'waves': [], 'terminal': {'kind': 'S', 'axis': 2,
                                      'left': leaf('I'), 'right': leaf(waves=wave)}}}
    projected = {**base, 'tree': project(base['tree'], '1')}
    validate_branch_extension(base, projected, '1')
    passed.append('owned_open_projection_preserves_old_wave')
    def mutate(name, fn):
        wrong = copy.deepcopy(projected)
        fn(wrong)
        rejects(name, lambda: validate_branch_extension(base, wrong, '1'))
    mutate('old_open_wave_prefix_lost', lambda x: x['tree']['terminal']['right'].update(waves=[]))
    mutate('exterior_sibling_modified', lambda x: x['tree']['terminal']['left'].update(terminal={'kind': 'I'}))
    mutate('exterior_sibling_lost', lambda x: x['tree']['terminal'].pop('left'))
    mutate('ancestor_axis_changed', lambda x: x['tree']['terminal'].update(axis=3))
    mutate('ancestor_waves_changed', lambda x: x['tree'].update(waves=wave))
    mutate('parent_envelope_changed', lambda x: x.update(rule='wrong'))
    refreshed = copy.deepcopy(base)
    refreshed['tree']['terminal']['right']['terminal'] = {
        'kind': 'S', 'axis': 1, 'left': leaf('I'), 'right': leaf()}
    refreshed_projection = {**refreshed, 'tree': project(refreshed['tree'], '1')}
    validate_branch_extension(refreshed, refreshed_projection, '1')
    passed.append('refreshed_target_partial_subtree_accepted')
    wrong_paid = copy.deepcopy(refreshed_projection)
    wrong_paid['tree']['terminal']['right']['terminal']['left']['terminal'] = {'kind': 'O'}
    rejects('refreshed_target_paid_leaf_changed', lambda:
            validate_branch_extension(refreshed, wrong_paid, '1'))

    # Execute the exact new verify function with a cheap artificial propagation
    # fixture. This exercises its true depth guard and exact Fraction midpoint
    # cover, not production RHO5 arithmetic. It grants no mathematical credit.
    module = ast.parse(Path(bp.__file__).read_text())
    verify_node = next(n for n in module.body if isinstance(n, ast.FunctionDef) and n.name == 'verify')
    from collections import Counter
    fixture_db = SimpleNamespace(validate_profile=lambda p: None,
                                 common_contract=lambda box, profile: box)
    fixture_box = {'status': 'BOUNDED', 'aux_image': [['0', '1'] for _ in range(24)]}
    env = {'binding': lambda parent: {}, 'prefix_image': lambda parent, cc:
           (copy.deepcopy(fixture_box), {'waves': 0, 'bounds': 0}),
           'db': fixture_db, 'Counter': Counter, 'Q': Fraction, 'json_hash': digest}
    exec(compile(ast.Module(body=[verify_node], type_ignores=[]), '<actual_deep_verify_fixture>', 'exec'), env)
    checked = env['verify']({'index': 0}, {'profile': 'fixture', 'tree': deep}, True, True)
    assert checked['counts']['maxdepth'] == MAX_DEPTH and checked['counts']['O'] == MAX_DEPTH + 1
    passed.append('actual_new_verify_depth500_exact_midpoint_fixture')
    rejects('actual_new_verify_depth501_rejected', lambda: env['verify'](
        {'index': 0}, {'profile': 'fixture', 'tree': chain(MAX_DEPTH + 1)}, True, True))
    rejects('actual_new_verify_open_not_complete', lambda: env['verify'](
        {'index': 0}, {'profile': 'fixture', 'tree': leaf()}, False, True))
    rejects('actual_new_verify_false_interval_terminal', lambda: env['verify'](
        {'index': 0}, {'profile': 'fixture', 'tree': leaf('I')}, True, True))
    return {'status': 'SMALL_CONTROLS_PASS', 'count': len(passed), 'controls': passed,
            'fixture_is_not_a_rho5_proof': True, 'old_large_trees_replayed': 0,
            'new_rule_identity': bp.rule_hash()}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('root', type=Path)
    p.add_argument('--known-parent', type=Path)
    p.add_argument('--known-certificate', type=Path)
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    if bool(a.known_parent) != bool(a.known_certificate):
        p.error('Known parent and certificate must be supplied together')
    result = small_controls(a.root)
    if a.known_parent:
        bp = load_protocol(a.root)
        parent = json.loads(a.known_parent.read_text())
        old = json.loads(a.known_certificate.read_text())
        if old.get('rule') != OLD_RULE:
            raise ValueError('Known control must be original V44')
        if counts(old['tree'])['nodes'] > 15:
            raise ValueError('Known fixture must be small (at most 15 nodes)')
        new = bp.wrap(parent, old['tree'], old['profile'])
        result['one_small_real_fixture'] = bp.verify(parent, new, allow_open=True, cross_check=True)
        result['known_input_sha256'] = digest(old)
        result['known_migrated_sha256'] = digest(new)
    if a.output:
        atomic(a.output, result)
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
