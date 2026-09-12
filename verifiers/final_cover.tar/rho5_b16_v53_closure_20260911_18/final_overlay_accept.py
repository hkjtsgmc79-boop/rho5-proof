#!/usr/bin/env python3
"""Compose paid proof receipts and bind all four residuals of the actual root.

This is a production acceptance adapter, not a new mathematical leaf verifier.
The operator seals CONFIG only after the joint producer has really run on X.
Every proof input and producer must be byte-pinned; no arbitrary PASS is accepted.
Only the caller-selected output directory is written. No state edit or signal.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import copy
import hashlib
import json
import os
import sys
import time

sys.setrecursionlimit(10000)
JOINT = 'RHO5_B15_B16_V53_COMPLETE_ANCHOR_V1'
CONFIG_SCHEMA = 'RHO5_B16_V53_FINAL_OVERLAY_CONFIG_V1'
ROOT_SHA = '8e138dce9a65e49252a1f4714229b1ca95227943913f1eeefdf51714810a563c'
PARTIAL_SHA = 'b4515303844ba40537cc083d7c6be71cce9f142d3bcbf9023ce2bbeb674988f7'
PARENT_SHA = '9d7f10cf242dddc51c6fd5a03fed4adf9f4084bb9c3584e801f4693ce093f780'
COMPOSER_SHA = '29f94de569c486e79e709d9fb03dd58fccc052721d6bdd60920155c6ec8f6e89'
INDICES = (338726, 435003, 563285, 675104)
ANCHOR = '10011101'
TASK_ID = '435003_bebe09509f4b934c5496'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                     ensure_ascii=False).encode()).hexdigest()


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(4 * 1024**2), b''):
            h.update(block)
    return h.hexdigest()


def member(root, file):
    path = (root / file).resolve()
    need(path.is_relative_to(root), 'Input escapes its sealed evidence root')
    return path


class Inputs:
    def __init__(self):
        self.checked = {}

    @staticmethod
    def stamp(path):
        s = Path(path).stat()
        return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)

    def check(self, path, expected):
        path = Path(path).resolve()
        before = self.stamp(path)
        old = self.checked.get(str(path))
        if old:
            need(old == (before, expected), 'Proof file identity changed or conflicting SHA')
            return path
        need(isinstance(expected, str) and len(expected) == 64, 'Missing exact SHA pin')
        need(sha(path) == expected and self.stamp(path) == before,
             'Pinned proof/producer bytes differ: ' + str(path))
        self.checked[str(path)] = (before, expected)
        return path

    def json(self, root, ref):
        path = self.check(member(root, ref['file']), ref['sha256'])
        with path.open() as stream:
            value = json.load(stream)
        need(self.stamp(path) == self.checked[str(path)][0], 'Evidence changed while decoding')
        return value

    def manifest(self, root, rows):
        need(isinstance(rows, list) and bool(rows), 'Empty acceptance evidence manifest')
        seen = set()
        for row in rows:
            need(row['file'] not in seen, 'Duplicated manifest member')
            seen.add(row['file'])
            self.check(member(root, row['file']), row['sha256'])

    def finish(self):
        for path, (stamp, _) in self.checked.items():
            need(self.stamp(path) == stamp, 'Input changed before final composition')

    def rows(self):
        return [{'file': path, 'sha256': entry[1]}
                for path, entry in sorted(self.checked.items())]


def old_open_paths(tree):
    answer, pending = [], [(tree, '')]
    while pending:
        node, path = pending.pop()
        term = node['terminal']
        if term['kind'] == 'O':
            answer.append(path)
        elif term['kind'] == 'S':
            pending += [(term['left'], path + '0'), (term['right'], path + '1')]
        else:
            need(term['kind'] in ('I', 'A', 'C', 'H'), 'Unexpected original anchor terminal')
    return sorted(answer)


def bind_anchor(base, partial):
    need({k: v for k, v in base.items() if k != 'tree'} ==
         {k: v for k, v in partial.items() if k != 'tree'}, 'Anchor/source header differs')
    left, right, ancestors = base['tree'], partial['tree'], []
    for depth, bit in enumerate(ANCHOR):
        a, b = left['terminal'], right['terminal']
        need(a.get('kind') == b.get('kind') == 'S' and a['axis'] == b['axis']
             and left['waves'] == right['waves'], 'Original d8 source ancestry differs')
        ancestors.append({'depth': depth, 'side': bit, 'axis': a['axis'],
                          'waves_sha256': digest(left['waves'])})
        side = 'left' if bit == '0' else 'right'
        left, right = a[side], b[side]
    need(left['terminal'] == {'kind': 'O'}, 'Original d8 responsibility is not an OPEN')
    need(right['waves'][:len(left['waves'])] == left['waves'],
         'Complete-anchor source lost the original target wave prefix')
    return {'status': 'COMPLETE_JOINT_SOURCE_BOUND_TO_ORIGINAL_ANCHOR_O',
            'ancestors': ancestors, 'original_target_waves_sha256': digest(left['waves']),
            'complete_source_target_waves_sha256': digest(right['waves']),
            'added_target_waves_verified_by_joint_producer': True,
            'new_mathematical_replay_performed': False}


def validate_parent_receipt(receipt, index, root, inputs):
    need(receipt['schema'] == 'RHO5_ALPHA_COMPOSITE_PARENT_V1' and receipt['index'] == index,
         'Wrong inherited parent receipt')
    need(receipt['composition_implementation_sha256'] == COMPOSER_SHA,
         'Unrecognized inherited parent receipt producer')
    inputs.check(root / 'alpha_parent_cover.py', COMPOSER_SHA)
    need(digest(receipt['evidence_manifest']) == receipt['evidence_manifest_sha256'],
         'Inherited evidence manifest digest differs')
    inputs.manifest(root, receipt['evidence_manifest'])
    rows = receipt['targets']
    paths = [row['target_path'] for row in rows]
    need(len(set(paths)) == len(paths) == receipt['total_original_targets']
         and sorted(paths) == sorted(receipt['original_open_paths']),
         'Inherited parent target cover incomplete or duplicated')
    need(sum(row['closed'] is True for row in rows) == receipt['covered_targets'],
         'Inherited parent covered count differs')
    need(receipt['covered_targets'] + receipt['open_targets'] == len(rows),
         'Inherited parent total differs')
    need(not receipt['whole_root_credit'] and not receipt['old_frozen_rule_acceptance'],
         'An independent parent receipt was mislabeled as old-root proof')
    if index == 435003:
        need(receipt['status'] == 'OPEN' and receipt['covered_targets'] == 239
             and receipt['total_original_targets'] == 240 and receipt['open_targets'] == 1,
             'Expected the already accepted 239/240 parent basis')
        open_rows = [r for r in rows if not r['closed']]
        need(len(open_rows) == 1 and open_rows[0]['target_path'] == ANCHOR
             and open_rows[0]['task_id'] == TASK_ID, 'Unpaid original task differs')
    else:
        need(receipt['status'] == 'STRICT_ALPHA_COMPOSITE_PARENT_ACCEPTED'
             and receipt['open_targets'] == 0, 'Inherited alpha parent is incomplete')


def actual_root_binding(data, model, parent_records):
    """Read all flat node positions, but replay dyadic boxes on just four paths.

    Earlier Fraction cold acceptance pays all other mathematical terminals.
    This only proves the FOUR ACTUAL ROOT O's are these exact parent boxes.
    """
    need(data.get('task') is None and data.get('root_path') == '', 'Not the original whole root')
    need(model.get('branch_coordinates') == 17 and len(model['frame_order']) == 17,
         'Incorrect frozen B17 frame model')
    root_box = [[Q(v) for v in model['bounds'][name]] for name in model['frame_order']]
    targets = {p['path']: index for index, p in parent_records.items()}
    need(len(targets) == 4, 'Root parents have duplicate paths')
    prefixes = {path[:n] for path in targets for n in range(len(path) + 1)}
    pending = [('', [])]
    opened, kinds = {}, {}
    allowed = {'E','C','H','V','G','U40','W40','U41','G41','B42','C42','B44'}
    nodes = data['nodes']
    for position, node in enumerate(nodes):
        need(pending, 'Unexpected extra root node')
        path, route = pending.pop()
        kind = node.get('kind')
        kinds[kind] = kinds.get(kind, 0) + 1
        if kind == 'S':
            axis = node['axis']
            need(set(node) == {'kind', 'axis'} and type(axis) is int and 0 <= axis < 17,
                 'Bad original root split')
            left_path, right_path = path + '0', path + '1'
            pending += [(right_path, route + [(axis, 1)] if right_path in prefixes else []),
                        (left_path, route + [(axis, 0)] if left_path in prefixes else [])]
        elif kind == 'O':
            need(node == {'kind': 'O'} and path in targets, 'Unbound actual old-root OPEN')
            index = targets[path]
            need(position == index and index not in opened, 'Original root node index differs')
            box = copy.deepcopy(root_box)
            for axis, side in route:
                lo, hi = box[axis]
                mid = (lo + hi) / 2
                need(lo < mid < hi, 'Degenerate original root split')
                box[axis][0 if side else 1] = mid
            parent = parent_records[index]
            expected = [[Q(v) for v in pair] for pair in parent['box']]
            need(box == expected, 'Accepted parent is bound to a different actual root box')
            encoded_box = [[str(v) for v in pair] for pair in box]
            need(digest(encoded_box) == parent['box_sha256'], 'Actual root box hash differs')
            opened[index] = {'index': index, 'path': path, 'actual_node_kind': 'O',
                             'box_sha256': parent['box_sha256'], 'route_depth': len(route),
                             'source': 'EXACT_DYADIC_ROUTE_IN_ALREADY_ACCEPTED_ACTUAL_ROOT'}
        else:
            need(kind in allowed, 'Unknown original root terminal')
    need(not pending and set(opened) == set(INDICES), 'Actual root does not have exactly these four OPEN parents')
    return {'status': 'ALL_FOUR_ACTUAL_ROOT_OPEN_BOXES_BOUND', 'root_sha256': ROOT_SHA,
            'actual_node_count': len(nodes), 'actual_kinds': kinds,
            'bound_parents': [opened[i] for i in INDICES],
            'old_terminal_mathematics_replayed': False,
            'exact_dyadic_source_paths_reconstructed': 4}


def atomic(path, value):
    path = Path(path)
    temp = path.with_name(path.name + '.tmp.' + str(os.getpid()))
    with temp.open('x') as stream:
        json.dump(value, stream, ensure_ascii=False, sort_keys=True, indent=2)
        stream.write('\n'); stream.flush(); os.fsync(stream.fileno())
    os.replace(temp, path)


def accept(config_file, config_sha):
    inputs = Inputs()
    config_file = Path(config_file).resolve()
    config = inputs.json(config_file.parent, {'file': config_file.name, 'sha256': config_sha})
    need(config['schema'] == CONFIG_SCHEMA, 'Wrong sealed composition config')
    roots = {k: Path(config[k]).resolve() for k in ('deep_root', 'proof_root', 'independent_root')}
    need(all(str(p).startswith('/root/microscope_ws/') for p in roots.values()),
         'Production composition is restricted to the authorized X workspace')
    os.nice(max(0, 10 - os.getpriority(os.PRIO_PROCESS, 0)))
    deep, proof, independent = (roots[k] for k in ('deep_root', 'proof_root', 'independent_root'))
    joint = inputs.json(proof, config['joint_receipt'])
    need(joint['schema'] == JOINT and joint['status'] == 'COMPLETE_ANCHOR_ALPHA_SAFE'
         and joint['parent_index'] == 435003 and joint['parent_sha256'] == PARENT_SHA
         and joint['task_id'] == TASK_ID and joint['anchor_path'] == ANCHOR
         and joint['anchor_closed'] is True and joint['remaining_sources'] == []
         and joint['semantic'] == 'ALPHA_SAFE' and joint['whole_parent_closed'] is False
         and joint['source_partial_sha256'] == PARTIAL_SHA, 'Incomplete or differently scoped joint acceptance')
    need(joint['paid_leaves'] == 54, 'Joint acceptance does not pay all54 leaves')
    need(joint['mathematical_replay_executed_this_run'] is True,
         'Joint producer did not execute mathematical replay')
    need(joint['producer_file_sha256'] == config['joint_producer']['sha256'],
         'Joint receipt producer identity differs from the operator pin')
    inputs.check(member(proof, config['joint_producer']['file']), config['joint_producer']['sha256'])
    inputs.manifest(proof, joint['evidence_manifest'])
    need(config['source_partial']['sha256'] == PARTIAL_SHA, 'Wrong complete source partial')
    partial_record = inputs.json(proof, config['source_partial'])
    partial = partial_record.get('certificate', partial_record)

    receipts, parents = {}, {}
    need(set(config['parent_receipts']) == {str(i) for i in INDICES}, 'Four parent receipts required')
    for index in INDICES:
        receipt = inputs.json(deep, config['parent_receipts'][str(index)])
        validate_parent_receipt(receipt, index, deep, inputs)
        parents[index] = inputs.json(deep, {'file': receipt['parent_file'], 'sha256': receipt['parent_sha256']})
        need(parents[index]['index'] == index, 'Parent file index differs')
        receipts[index] = receipt
    old = receipts[435003]
    need(old['parent_sha256'] == PARENT_SHA, 'Joint proof has another physical parent')
    base = inputs.json(deep, {'file': old['anchor_file'], 'sha256': old['anchor_sha256']})
    need(old_open_paths(base['tree']) == sorted(old['original_open_paths']), 'Original target partition differs')
    binding = bind_anchor(base, partial)
    new_parent = copy.deepcopy(old)
    new_parent.update(schema='RHO5_SOURCE_COMPOSITE_PARENT_V1',
        rule='RHO5_PAID_PARENT_PLUS_COMPLETE_JOINT_ANCHOR_V1',
        status='STRICT_SOURCE_COMPOSITE_PARENT_ACCEPTED', covered_targets=240,
        open_targets=0, still_open_paths=[], epoch=time.time(),
        mathematical_replay_performed=False,
        old_parent_receipt=config['parent_receipts']['435003'],
        joint_anchor_receipt=config['joint_receipt'], joint_source_binding=binding,
        joint_proof_root=str(proof), joint_evidence_manifest=joint['evidence_manifest'])
    for row in new_parent['targets']:
        if row['target_path'] == ANCHOR:
            row.update(status='COVERED_BY_SOURCE_COMPOSITE', closed=True,
                       independent_mathematical_receipt_reused=True,
                       evidence={'joint_receipt': config['joint_receipt'], 'source_binding': binding})
    new_parent['coverage_counts']['OPEN'] = 0
    new_parent['coverage_counts']['COVERED_BY_SOURCE_COMPOSITE'] = 1
    new_parent['source_signature'] = digest({'basis': old['source_signature'],
                                            'joint': config['joint_receipt'], 'binding': binding})

    ready = inputs.json(independent, config['old_root_acceptance'])
    need(ready['status'] == 'ORIGINAL_FULL_FRACTION_ROOT_ACCEPTED_ADOPTION_READY'
         and ready['root_sha256'] == ROOT_SHA and ready['now_formally_proved_parent_count'] == 465
         and ready['total_parent_count'] == 469 and ready['remaining_unclosed_count'] == 4
         and sorted(ready['remaining_unclosed_indices']) == list(INDICES), 'Paid whole-root acceptance differs')
    cold = inputs.json(independent, {'file': ready['cold_receipt_file'],
                                    'sha256': ready['cold_receipt_file_sha256']})
    need(cold['tree_sha256'] == ROOT_SHA and cold['backend'] == 'fraction'
         and cold['open'] == 4 and cold['nodes'] == 749693 and cold['splits'] == 374846,
         'Missing actual paid Fraction root acceptance')
    root = inputs.json(independent, {'file': ready['root_file'], 'sha256': ROOT_SHA})
    model_root = Path(config.get('root_model_root', str(independent))).resolve()
    need(str(model_root).startswith('/root/microscope_ws/'), 'Model root escapes X workspace')
    model = inputs.json(model_root, config['root_model'])
    need(root['model_sha256'] == config['root_model']['sha256'], 'Actual root/model identity differs')
    root_binding = actual_root_binding(root, model, parents)
    del root
    new_parent['whole_root_credit'] = False
    new_parent['composition_implementation_sha256'] = sha(__file__)
    new_parent['joint_rule'] = JOINT
    inputs.finish()
    out = Path(config['output_directory']).resolve()
    need(str(out).startswith('/root/microscope_ws/'), 'Output escapes X workspace')
    out.mkdir(parents=True, exist_ok=True)
    need(not any((out / n).exists() for n in ('PARENT_435003_COMPLETE.json', 'ROOT_COMPLETE_OVERLAY.json')),
         'Refusing to overwrite a prior complete acceptance')
    atomic(out / 'PARENT_435003_COMPLETE.json', new_parent)
    overlay = {
        'schema': 'RHO5_ACTUAL_ROOT_COMPLETE_SOURCE_OVERLAY_V1',
        'status': 'ACTUAL_ROOT_ALL_OPEN_PARENTS_COVERED',
        'epoch': time.time(), 'root_sha256': ROOT_SHA,
        'old_root_acceptance': config['old_root_acceptance'],
        'old_root_open_count': 4, 'effective_open_count': 0,
        'old_rule_accepted_parents': 465, 'independent_alpha_parents': 3,
        'independent_source_composite_parents': 1, 'complete_parents': 469,
        'actual_root_binding': root_binding,
        'parent_receipts': {str(i): config['parent_receipts'][str(i)] for i in INDICES if i != 435003},
        'new_parent_receipt': {'file': str(out / 'PARENT_435003_COMPLETE.json'),
                               'sha256': sha(out / 'PARENT_435003_COMPLETE.json')},
        'joint_anchor_receipt': config['joint_receipt'],
        'evidence_manifest': inputs.rows(),
        'producer_file_sha256': sha(__file__), 'sealed_config_sha256': config_sha,
        'old_frozen_rule_root_modified': False,
        'old_frozen_rule_zero_open_claimed': False,
        'new_math_replayed_by_this_composer': False,
        'whole_B_closed_by_independent_complete_overlay': True,
        'macro_ledger_requires_project_master_update': True,
        'production_processes_stopped_by_this_composer': False,
        'production_mutable_state_modified_by_this_composer': False,
    }
    atomic(out / 'ROOT_COMPLETE_OVERLAY.json', overlay)
    return {k: overlay[k] for k in ('status','root_sha256','effective_open_count','complete_parents')}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--config-sha256', required=True)
    args = parser.parse_args()
    print(json.dumps(accept(args.config, args.config_sha256), ensure_ascii=False, indent=2))
