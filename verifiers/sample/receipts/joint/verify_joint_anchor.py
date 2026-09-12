#!/usr/bin/env python3
"""Execute pinned V53 and B16 replays, then bind their exact source cover.

This is a new independent composition rule. Frozen child verifiers are never
modified. V53's two-OPEN receipt remains partial; only the new ledger is complete.
There is deliberately no option to trust cached child PASS receipts.
"""
from pathlib import Path, PurePosixPath
from collections import Counter
import argparse
import copy
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
import traceback
import zipfile

RULE = 'RHO5_B15_B16_V53_COMPLETE_ANCHOR_V1'
STATUS = 'COMPLETE_ANCHOR_ALPHA_SAFE'
SEMANTIC = 'ALPHA_SAFE'
TASK = '435003_bebe09509f4b934c5496'
ANCHOR = '10011101'
PARENT = '9d7f10cf242dddc51c6fd5a03fed4adf9f4084bb9c3584e801f4693ce093f780'
PARTIAL = 'b4515303844ba40537cc083d7c6be71cce9f142d3bcbf9023ce2bbeb674988f7'
INDEX = 'bc28ba42601c09f89e32086445a6ba3424e5fe2201d2e66b72844fab66cb67b0'
INPUT_ZIP = 'cc22b378fc004d0e14b4b1c5e71c76b0edc517e71884aaf95d93867eeab674b2'
PENDING = ('10011101100111', '10011101101')
B16_RULE = 'B16_CANONICAL_PREFIX_TWO_CHART_GAMMA_V1'
GAMMA_SEMANTIC = 'GAMMA_EXCLUDED_CANONICAL_SOURCE'
PINS = {
    'v53': {
        'MANIFEST_SHA256.json': '58831b8529e37095abeba8f9ceeb41f98245a9aab530ef2176c60662438c30df',
        'verify_all.py': 'ec243398759be52d8e16c5e1c5cdaf0ea7138ab6890084ccb6a34c0aef57ee6a',
        'scripts/v53_verify.py': 'eddb6fd88011eb0fce9de1bb5cb1ff0b60aef5418924612b5777fa802767c49a',
        'scripts/v53_boot.py': '91ef0a7ace05ed6b467b6dfdf34ca030b90e9a1b6b621760361bf30525b127b7',
        'V53_B16_INTERFACE.json': '31c5414cb242fe334f454417a6d07a659736028ad0251ebd2bb8665bdd2ba886',
    },
    'b16': {
        'MANIFEST_SHA256.json': '753e63da04f7b66e396addc7afb171dbf693de2c2b1df0e205460683f1f31d38',
        'PROOF_PAYLOAD_SHA256.json': '05ffe70f25190657b8aed50f52855f4796a322ec120a350e847ce516852206be',
        'verify_all.py': 'a775a5848104146cae9e5b779dfcd48ff0f16624c7afdbe6648c697aa9b0f4ff',
    },
}
SPECS = {
    '10011101101': (11, '51684d5336ffbce69e5e413ae7fe09285eb81b7c45c9d873b934f78d055aa4b4',
                   '5d4fb071387fba8ddd91d8cbb939706be545d746ecb4c951068bf92744128825'),
    '10011101100111': (14, '68a09e4ea489e50f0a87e87c2ddd2f57fe79361c01c518647b03c0f4d1325ea8',
                      '45efdbaac9cb0bc52d72cd00b842aedbfb2d7dec096f83ad8e7670d2661edbf8'),
}
OLD_CLASSES = {'OLD_GAMMA_EXCLUSION_I', 'OLD_GAMMA_EXCLUSION_C',
               'OLD_ALPHA_SAFE_H', 'OLD_ALPHA_SAFE_A', 'B14_ALPHA_SAFE',
               'NEW_V53_GAMMA_EXCLUSION_C', 'B15_GAMMA_EXCLUDED_CANONICAL_SOURCE'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def jsha(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(',', ':'),
                                     ensure_ascii=False).encode()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_name(path.name + '.tmp')
    temp.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    os.replace(temp, path)


def safe_relative(root, name):
    p = PurePosixPath(name)
    require(type(name) is str and not p.is_absolute() and '..' not in p.parts
            and '\\' not in name, 'Unsafe manifest path')
    file = root.joinpath(*p.parts)
    require(not file.is_symlink() and file.resolve().is_relative_to(root.resolve()),
            'Escaping or symlink input')
    return file


def package_integrity(v53, b16):
    records = {}
    for key, root in [('v53', v53), ('b16', b16)]:
        for name, expected in PINS[key].items():
            require(sha(safe_relative(root, name)) == expected, 'Changed pinned ' + key + '/' + name)
        manifest = read(root / 'MANIFEST_SHA256.json')
        expect_count = 25 if key == 'v53' else 190
        require(len(manifest['files']) == expect_count, 'Wrong frozen manifest cardinality')
        for name, expected in manifest['files'].items():
            require(sha(safe_relative(root, name)) == expected, 'Frozen input mismatch: ' + name)
        files = dict(manifest['files'])
        files['MANIFEST_SHA256.json'] = sha(root / 'MANIFEST_SHA256.json')
        if key == 'b16':
            payload = read(root / 'PROOF_PAYLOAD_SHA256.json')
            require(payload['schema'] == 'B16_EXACT_PAYLOAD_V1' and len(payload['files']) == 179,
                    'Wrong B16 mathematical payload')
            for name, expected in payload['files'].items():
                require(files.get(name) == expected, 'Payload/outer manifest mismatch')
        records[key] = {'package_directory': str(root), 'files': files,
                        'manifest_file_sha256': sha(root / 'MANIFEST_SHA256.json')}
    return records


def source_inputs(v53, b16):
    archive = v53 / 'inputs/RHO5_REMAINING_THREE_SOURCES.zip'
    require(sha(archive) == INPUT_ZIP, 'Wrong V53 input archive')
    with zipfile.ZipFile(archive) as z:
        names = z.namelist()
        require(len(names) == len(set(names)), 'Duplicate source archive member')
        parent_name = 'previous_source_snapshot/alpha_v1/sources/' + PARENT + '_435003_parent.json'
        pairs = {parent_name: b16 / 'inputs/parent.json',
                 'latest_sources/PARTIAL_DISCOVERY.json': b16 / 'inputs/PARTIAL_DISCOVERY.json',
                 'SOURCE_INDEX.json': b16 / 'inputs/SOURCE_INDEX.json'}
        for path, (dep, _, _) in SPECS.items():
            pairs['latest_sources/435003_' + path + '_projection.json'] = b16 / ('inputs/projection_%d.json' % dep)
        for name, file in pairs.items():
            require(z.read(name) == file.read_bytes(), 'Child inputs differ: ' + name)
    require(sha(b16 / 'inputs/parent.json') == PARENT, 'Wrong parent')
    require(sha(b16 / 'inputs/PARTIAL_DISCOVERY.json') == PARTIAL, 'Wrong partial')
    require(sha(b16 / 'inputs/SOURCE_INDEX.json') == INDEX, 'Wrong source index')
    partial = read(b16 / 'inputs/PARTIAL_DISCOVERY.json')
    return partial


def by_path(rows):
    require(type(rows) is list, 'Expected path records')
    result = {}
    for r in rows:
        require(type(r) is dict and type(r.get('path')) is str, 'Malformed path record')
        require(r['path'] not in result, 'Duplicate source/path')
        result[r['path']] = r
    return result


def validate_partial(ledger):
    require(ledger['schema'] == 'V53_DEPTH8_ANCHOR_COVERAGE_V1', 'Wrong original ledger')
    require(ledger['status'] == 'PARTIAL_ALPHA_COVERAGE_TWO_B16_SOURCES_OPEN'
            and ledger['anchor_closed'] is False, 'V53 must remain partial')
    require(type(ledger['parent_index']) is int and ledger['parent_index'] == 435003
            and ledger['parent_sha256'] == PARENT and ledger['task_id'] == TASK
            and ledger['anchor_path'] == ANCHOR and ledger['source_partial_sha256'] == PARTIAL
            and ledger['source_index_sha256'] == INDEX, 'Wrong original ledger source')
    require(ledger['remaining_sources'] == list(PENDING), 'Wrong pending list')
    leaves = by_path(ledger['leaves'])
    require(len(leaves) == 54, 'Expected 54 anchor leaves')
    require(sorted(p for p, r in leaves.items() if r['classification'] == 'OPEN_B16') == sorted(PENDING),
            'Missing or substituted B16 slot')
    require(all(r['classification'] in OLD_CLASSES | {'OPEN_B16'} for r in leaves.values()),
            'Unsupported old classification')
    nodes = by_path(ledger['visited_nodes'])
    visited_inside = {p for p in nodes if p.startswith(ANCHOR)}
    seen = set()
    def walk(path):
        require(path in nodes and path not in seen, 'Missing/repeated coverage node')
        seen.add(path)
        if path in leaves:
            require(nodes[path]['kind'] != 'S', 'Leaf/split collision')
        else:
            require(nodes[path]['kind'] == 'S', 'Unaccounted leaf')
            walk(path + '0'); walk(path + '1')
    walk(ANCHOR)
    require(seen == visited_inside and len(seen) == 107, 'Incomplete binary partition')
    require(ledger['counts']['nodes'] == 107 and ledger['counts']['splits'] == 53
            and ledger['counts']['OPEN_B16'] == 2, 'Wrong original coverage counts')
    return leaves, nodes


def bind_children(ledger, result, interface):
    leaves, nodes = validate_partial(ledger)
    require(result['rule'] == B16_RULE and result['status'] == GAMMA_SEMANTIC
            and result['source_count'] == 2, 'Wrong actual B16 result')
    require(result['payload_integrity']['files_checked'] == 179
            and result['payload_integrity']['manifest_sha256'] == PINS['b16']['PROOF_PAYLOAD_SHA256.json'],
            'B16 result payload mismatch')
    require(interface['schema'] == 'V53_B16_FUTURE_SOURCE_INTERFACE_V1'
            and interface['parent_index'] == 435003 and interface['anchor_task_id'] == TASK
            and interface['anchor_path'] == ANCHOR and interface['partial_source_sha256'] == PARTIAL
            and interface['source_index_sha256'] == INDEX, 'Wrong B16 interface')
    slots = by_path(interface['slots'])
    require(set(slots) == set(PENDING), 'Missing interface slot')
    children = {}
    for child in result['results']:
        source = child['source']; path = source['path']
        require(path in SPECS and path not in children, 'Wrong/duplicate B16 source')
        dep, projection, image = SPECS[path]; slot = slots[path]; leaf = leaves[path]
        require(child['status'] == GAMMA_SEMANTIC and source['index'] == 435003
                and source['anchor_task_id'] == TASK and source['anchor_path'] == ANCHOR
                and source['parent_raw_sha256'] == PARENT and source['latest_partial_raw_sha256'] == PARTIAL
                and source['projection_raw_sha256'] == projection and source['image_sha256'] == image,
                'B16 exact source binding mismatch')
        require(source['source_depth'] == dep and source['suffix'] == path[len(ANCHOR):]
                and source['whole_task_covered'] is False and source['whole_parent_covered'] is False,
                'Unsupported child scope')
        require(jsha(source['aux_image']) == image and source['parent_binding'] == {
            k: v for k, v in ledger['_source_header'].items() if k != 'profile'}, 'Image/header mismatch')
        require(slot['parent_raw_sha256'] == PARENT and slot['expected_projection_sha256'] == projection
                and slot['rebuilt_entry_image_sha256'] == image
                and slot['complete_source_coverage_required'] is True,
                'Child does not satisfy fixed interface')
        require(leaf['classification'] == 'OPEN_B16' and leaf['source_image_sha256'] == image
                and leaf['evidence']['projection_sha256'] == projection, 'Wrong actual replay slot')
        visits = source['visited_ancestors_and_target']
        require([x['path'] for x in visits] == [path[:d] for d in range(len(path)+1)],
                'Missing/reordered complete ancestor sequence')
        interface_visits = by_path(slot['ancestor_path_records'])
        require(set(interface_visits) == {x['path'] for x in visits}, 'Wrong interface lineage extent')
        normalized = []
        for depth, event in enumerate(visits):
            vp = event['path']; ve = nodes[vp]
            norm = {k: event[k] for k in ('path','waves','bounds','waves_sha256','kind','image_sha256')}
            if depth < len(path):
                require(event['side'] == path[depth] and event['depth'] == depth, 'Wrong source side/depth')
                norm.update(axis=event['axis'], midpoint=event['exact_midpoint'])
            require(norm == ve == interface_visits[vp], 'Replayed ancestor/image/axis/midpoint mismatch: ' + vp)
            normalized.append(norm)
        require(visits[-1]['kind'] == 'O' and visits[-1]['waves_sha256'] == slot['target_waves_sha256']
                == leaf['target_waves_sha256'], 'Cut-local waves mismatch')
        require(child['cover_lemma']['complete_labels'] == ['B1|N:L1-:L0+','B1|N:L1-:L2+']
                and child['cover_lemma']['beta_forced'] == '1', 'Incomplete canonical chart cover')
        require([br['label'] for br in child['branches']] == child['cover_lemma']['complete_labels']
                and all(br['status'] == 'CONDITIONAL_GAMMA_EXCLUDED' for br in child['branches']),
                'Missing accepted conditional branch')
        children[path] = {'source_path': path, 'semantic': GAMMA_SEMANTIC,
            'whole_source_covered': True, 'projection_file_sha256': projection,
            'source_image_sha256': image, 'cut_waves_sha256': slot['target_waves_sha256'],
            'certificate_file_sha256': child['certificate_file_sha256'],
            'accepted_child_record_sha256': jsha(child), 'ancestor_records_sha256': jsha(normalized),
            'conditional_graphs': 2, 'negative_controls_passed': child['negative_controls_passed']}
    require(set(children) == set(PENDING) and len(result['results']) == 2, 'Missing one complete B16 source')
    return children


def completed_ledger(original, children):
    ledger = copy.deepcopy(original)
    ledger.pop('_source_header', None)
    ledger['schema'] = RULE
    ledger['rule'] = RULE
    ledger['status'] = STATUS
    ledger['semantic'] = SEMANTIC
    for row in ledger['leaves']:
        if row['classification'] == 'OPEN_B16':
            row['previous_classification'] = 'OPEN_B16'
            row['classification'] = 'B16_GAMMA_EXCLUDED_CANONICAL_SOURCE'
            row['evidence'] = children[row['path']]
    counts = dict(ledger['counts']); counts.pop('OPEN_B16')
    counts['B16_GAMMA_EXCLUDED_CANONICAL_SOURCE'] = 2
    ledger.update(counts=counts, remaining_sources=[], anchor_closed=True,
                  whole_parent_closed=False, whole_B_closed=False, paid_leaves=54)
    return ledger


def validate_complete(ledger):
    require(ledger['schema'] == RULE and ledger['rule'] == RULE and ledger['status'] == STATUS
            and ledger['semantic'] == SEMANTIC, 'Mixed alpha coverage cannot be labelled gamma empty')
    require(ledger['anchor_closed'] is True and ledger['remaining_sources'] == []
            and ledger['paid_leaves'] == 54 and ledger['whole_parent_closed'] is False
            and ledger['whole_B_closed'] is False, 'Unsupported joint completion scope')
    rows = by_path(ledger['leaves'])
    require(len(rows) == 54 and all(x['classification'] in OLD_CLASSES |
            {'B16_GAMMA_EXCLUDED_CANONICAL_SOURCE'} for x in rows.values()), 'Unpaid/unknown completed leaf')
    require({p for p, r in rows.items() if r['classification'] == 'B16_GAMMA_EXCLUDED_CANONICAL_SOURCE'}
            == set(PENDING), 'Missing/duplicate completed B16 credit')
    require(any('ALPHA_SAFE' in x['classification'] for x in rows.values()), 'Lost inherited alpha leaves')


def negative_controls(ledger, result, interface, complete):
    checks = []
    def reject(name, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError, IndexError):
            checks.append({'name': name, 'rejected': True})
            return
        raise ValueError('Negative control accepted: ' + name)
    bad = copy.deepcopy(result); bad['results'][0]['source']['parent_raw_sha256'] = '0'*64
    reject('wrong_child_source', lambda: bind_children(ledger, bad, interface))
    bad = copy.deepcopy(result); bad['results'] = bad['results'][:1]
    reject('missing_child', lambda: bind_children(ledger, bad, interface))
    bad = copy.deepcopy(result); bad['results'][1] = copy.deepcopy(bad['results'][0])
    reject('duplicate_child', lambda: bind_children(ledger, bad, interface))
    bad = copy.deepcopy(interface); bad['slots'] = bad['slots'][:1]
    reject('missing_interface_slot', lambda: bind_children(ledger, result, bad))
    bad = copy.deepcopy(result); bad['results'][0]['source']['visited_ancestors_and_target'][0]['axis'] = 0
    reject('changed_ancestor_axis', lambda: bind_children(ledger, bad, interface))
    bad = copy.deepcopy(result); bad['results'][0]['source']['visited_ancestors_and_target'][-1]['waves_sha256'] = '0'*64
    reject('changed_target_wave_identity', lambda: bind_children(ledger, bad, interface))
    bad = copy.deepcopy(complete); bad['semantic'] = GAMMA_SEMANTIC
    reject('alpha_relabelled_gamma', lambda: validate_complete(bad))
    bad = copy.deepcopy(complete); bad['leaves'] = bad['leaves'][:-1]
    reject('missing_completed_leaf', lambda: validate_complete(bad))
    bad = copy.deepcopy(complete); bad['whole_parent_closed'] = True
    reject('premature_whole_parent_promotion', lambda: validate_complete(bad))
    return {'controls': checks, 'count': len(checks), 'scope': 'Structure and binding only; no duplicate mathematical replay'}


def run_child(command, log, root):
    started = time.time(); env = os.environ.copy()
    for key in list(env):
        if key.startswith('V53_') or key in ('PYTHONPATH', 'PYTHONHOME', 'PYTHONOPTIMIZE'):
            env.pop(key, None)
    env.update(PYTHONDONTWRITEBYTECODE='1', OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1',
               MKL_NUM_THREADS='1', NUMEXPR_NUM_THREADS='1')
    with log.open('w', encoding='utf-8') as f:
        process = subprocess.Popen(command, cwd=root, env=env, stdout=f, stderr=subprocess.STDOUT)
        try:
            code = process.wait()
        except BaseException:
            process.terminate(); process.wait(); raise
    require(code == 0, 'Frozen child replay failed, see ' + str(log))
    return {'command': command, 'returncode': code, 'started_epoch': started,
            'elapsed_seconds': time.time()-started, 'log_file': log.name, 'log_file_sha256': sha(log)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--v53-dir', required=True, type=Path)
    parser.add_argument('--b16-dir', required=True, type=Path)
    parser.add_argument('--output-dir', required=True, type=Path)
    args = parser.parse_args()
    require(__debug__, 'Optimized Python is not accepted by V53')
    v53, b16, out = args.v53_dir.resolve(), args.b16_dir.resolve(), args.output_dir.resolve()
    require(not out.exists() or not any(out.iterdir()), 'Refuse to mix with existing joint output')
    require(out != v53 and out != b16 and not out.is_relative_to(v53) and not out.is_relative_to(b16),
            'Joint outputs must be outside frozen packages')
    out.mkdir(parents=True, exist_ok=True)
    started = time.time()
    try:
        frozen = package_integrity(v53, b16)
        partial = source_inputs(v53, b16)
        write(out/'FROZEN_INPUT_FILES.json', frozen)
        commands = []
        commands.append(run_child([sys.executable, '-S', str(v53/'verify_all.py'), '--output',
            str(out/'V53_RESULT.json'), '--artifacts', str(out/'v53_artifacts')], out/'V53_REPLAY.log', v53))
        commands.append(run_child([sys.executable, '-S', str(b16/'verify_all.py'), '--output',
            str(out/'B16_RESULT.json')], out/'B16_REPLAY.log', b16))
        require(package_integrity(v53, b16) == frozen, 'Frozen inputs changed during replay')
        source_inputs(v53, b16)
        v53_result = read(out/'V53_RESULT.json')
        require(v53_result['status'] == 'V53_DEPTH19_COMPLETE_AND_ANCHOR_TWO_OPEN_EXACT_PASS'
                and v53_result['anchor_closed'] is False
                and v53_result['anchor_remaining_sources'] == list(PENDING), 'Wrong actual V53 result')
        ledger = read(out/'v53_artifacts/V53_ANCHOR_COVERAGE.json')
        ledger['_source_header'] = {k: v for k, v in partial['certificate'].items() if k != 'tree'}
        result = read(out/'B16_RESULT.json'); interface = read(v53/'V53_B16_INTERFACE.json')
        children = bind_children(ledger, result, interface)
        complete = completed_ledger(ledger, children); validate_complete(complete)
        controls = negative_controls(ledger, result, interface, complete)
        write(out/'JOINT_NEGATIVE_CONTROLS.json', controls)
        write(out/'COMPLETED_ANCHOR_LEDGER.json', complete)
        source = out/'source'; source.mkdir()
        for name in ('parent.json', 'PARTIAL_DISCOVERY.json', 'SOURCE_INDEX.json'):
            shutil.copyfile(b16/'inputs'/name, source/name)
        header = {k: v for k, v in partial['certificate'].items() if k != 'tree'}
        node = partial['certificate']['tree']; lineage = []
        visits = by_path(ledger['visited_nodes'])
        for depth, side in enumerate(ANCHOR):
            path = ANCHOR[:depth]; terminal = node['terminal']
            require(terminal['kind'] == 'S' and jsha(node['waves']) == visits[path]['waves_sha256']
                    and terminal['axis'] == visits[path]['axis'], 'Wrong saved preanchor lineage')
            lineage.append({'path': path, 'waves': node['waves'], 'axis': terminal['axis'],
                            'side': side, 'exact_midpoint': visits[path]['midpoint'],
                            'image_sha256': visits[path]['image_sha256']})
            node = terminal['left' if side == '0' else 'right']
        write(out/'SOURCE_BINDING.json', {'certificate_header': header,
            'parent_file': 'source/parent.json', 'parent_file_sha256': PARENT,
            'partial_file': 'source/PARTIAL_DISCOVERY.json', 'partial_file_sha256': PARTIAL,
            'preanchor_lineage': lineage, 'anchor_waves': node['waves'],
            'anchor_waves_sha256': jsha(node['waves']), 'anchor_image_sha256': visits[ANCHOR]['image_sha256']})
        evidence = out/'frozen_evidence'; evidence.mkdir()
        for key, root in [('v53', v53), ('b16', b16)]:
            for name in frozen[key]['files']:
                # Pin full packages in FROZEN_INPUT_FILES; retain direct proposal,
                # rule and manifest evidence alongside this actual replay.
                if name in PINS[key] or name.startswith('proof/'):
                    target = evidence/key/name; target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(root/name, target)
        shutil.copyfile(Path(__file__), out/'verify_joint_anchor.py')
        producer = sha(Path(__file__))
        write(out/'RUN_MANIFEST.json', {'rule': RULE, 'started_epoch': started,
            'producer_file_sha256': producer, 'python': sys.version, 'commands': commands,
            'frozen_input_manifests': {k: v['manifest_file_sha256'] for k,v in frozen.items()},
            'completed_epoch': time.time(), 'mathematical_replay_executed_this_run': True})
        manifest = [{'file': str(p.relative_to(out)), 'sha256': sha(p)}
                    for p in sorted(out.rglob('*')) if p.is_file()]
        receipt = {'schema': RULE, 'rule': RULE, 'status': STATUS, 'semantic': SEMANTIC,
            'parent_index': 435003, 'parent_sha256': PARENT, 'task_id': TASK,
            'anchor_path': ANCHOR, 'source_partial_sha256': PARTIAL,
            'anchor_closed': True, 'remaining_sources': [], 'whole_parent_closed': False,
            'whole_B_closed': False, 'paid_leaves': 54, 'original_partial_paid_leaves': 52,
            'new_B16_paid_leaves': 2, 'counts': complete['counts'],
            'producer_identity': RULE, 'producer_file': 'verify_joint_anchor.py',
            'producer_file_sha256': producer, 'evidence_manifest': manifest,
            'source_partial_file': 'source/PARTIAL_DISCOVERY.json',
            'parent_file': 'source/parent.json', 'source_binding_file': 'SOURCE_BINDING.json',
            'source_binding': read(out/'SOURCE_BINDING.json'),
            'completed_ledger_file': 'COMPLETED_ANCHOR_LEDGER.json',
            'accepted_children': children, 'frozen_input_files_file': 'FROZEN_INPUT_FILES.json',
            'child_output_hashes': {'V53_RESULT.json': sha(out/'V53_RESULT.json'),
                                  'B16_RESULT.json': sha(out/'B16_RESULT.json')},
            'negative_controls': controls, 'mathematical_replay_executed_this_run': True,
            'production_modified': False, 'completed_epoch': time.time(),
            'elapsed_seconds': time.time()-started}
        write(out/'ANCHOR_COMPLETE.json', receipt)
        print(json.dumps({'status': STATUS, 'anchor_path': ANCHOR, 'paid_leaves': 54,
                          'receipt_sha256': sha(out/'ANCHOR_COMPLETE.json')}, ensure_ascii=False), flush=True)
    except BaseException as exc:
        write(out/'JOINT_FAILURE.json', {'rule': RULE, 'error': str(exc),
            'traceback': traceback.format_exc(), 'epoch': time.time(), 'anchor_closed': False})
        raise


if __name__ == '__main__':
    main()
