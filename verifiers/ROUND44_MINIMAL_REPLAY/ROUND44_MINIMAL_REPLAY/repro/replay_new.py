#!/usr/bin/env python3
"""Minimal cold replay of a selected Round44 proof package, sequentially.

Run from a package containing SELECTION.json, repro/, and proofs/:
    python3 repro/replay_new.py . [--boost-include /path/to/boost]

Only complete selected trees are accepted. No discovery solver, partial-tree
volume, old tree, or P61 isolation computation is used by this entry point.
"""
from pathlib import Path
from fractions import Fraction
from datetime import datetime, timezone
import argparse
import contextlib
import hashlib
import importlib
import json
import os
import re
import subprocess
import sys

PASS = 'R44_MIDBAND_INTERVAL_EXACT_PASS'
PINNED = {
    'alpha.json': '9af09b9d6e584bba2a7cef7e9e3993f128fbc90744335eb0c22c8b11e0226959',
    'vendor/mc_exact_kernel.hpp': 'b0fbd7c98e52721c90a4f2460c26a2abaeb7420d69c74b38c4c5b49d3b394a63',
    'vendor/mc_verify.cpp': '3e036f955ff10158872b3870942c7df6129fa76d47964adde90a5193df6c20de',
}
PROOF_FILES = ('model.json', 'mc_exact_model.hpp', 'mc_exact_kernel.hpp', 'mc_verify.cpp', 'result.tree')
DEFAULT_DOCUMENTS = ('repro/ROUND44_NEW_NECESSITY_PROOF.md', 'repro/roots/CORE_R_PARTITION.md')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rational(value, label):
    require(isinstance(value, (str, int)) and not isinstance(value, bool),
            label + ' must be an exact rational string or integer, not a float')
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError('Invalid rational ' + label) from error


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def inside(package, relative, must_exist=True):
    rel = Path(relative)
    require(not rel.is_absolute(), 'Package paths must be relative')
    path = (package / rel).resolve(strict=must_exist)
    require(path != package and package in path.parents, 'Path escapes the package')
    return path


def relative(package, path):
    return Path(path).resolve().relative_to(package).as_posix()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def configure_single_cpu():
    for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
                'BLIS_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS', 'NUMEXPR_NUM_THREADS'):
        os.environ[key] = '1'
    os.environ['OMP_DYNAMIC'] = 'FALSE'
    os.environ['PYTHONDONTWRITEBYTECODE'] = '1'
    sys.dont_write_bytecode = True
    require(hasattr(os, 'getpriority') and hasattr(os, 'setpriority'),
            'This replay requires Unix process priority support')
    if os.getpriority(os.PRIO_PROCESS, 0) < 10:
        os.setpriority(os.PRIO_PROCESS, 0, 10)
    affinity = None
    if hasattr(os, 'sched_getaffinity') and hasattr(os, 'sched_setaffinity'):
        allowed = os.sched_getaffinity(0)
        require(bool(allowed), 'No available CPU affinity')
        os.sched_setaffinity(0, {min(allowed)})
        affinity = sorted(os.sched_getaffinity(0))
    return {'sequential': True, 'numerical_library_threads': 1,
            'nice': os.getpriority(os.PRIO_PROCESS, 0), 'cpu_affinity': affinity}


def proof_metadata(proof_id, data):
    case = data.get('head_case')
    branch = data.get('rbranch', 'all')
    fold = data.get('fold_i', False)
    require(case in ('I', 'II'), proof_id + ': selected proofs must be I or II; III is covered analytically')
    require(branch in ('all', 'low', 'high'), proof_id + ': unsupported r branch')
    require(isinstance(fold, bool) and (not fold or case == 'I'), proof_id + ': fold_i is permitted only for I')
    require(data.get('p_slice') == [None, None],
            proof_id + ': v1 k-only coverage rejects p-sliced models; a joint p/k coverage checker would be required')
    K, J = rational(data['klo'], proof_id + '.klo'), rational(data['khi'], proof_id + '.khi')
    require(K <= J, proof_id + ': reversed k interval')
    return {'id': proof_id, 'case': case, 'rbranch': branch, 'fold_i': fold,
            'K': str(K), 'J': str(J), 'target': str(rational(data['target'], proof_id + '.target'))}


def merge_closed(intervals):
    """Exact union; equality at a seam joins two CLOSED intervals."""
    merged = []
    for a, b, proof_id in sorted(intervals):
        require(a <= b, 'Reversed proof interval')
        if not merged or a > merged[-1]['J']:
            merged.append({'K': a, 'J': b, 'proof_ids': [proof_id]})
        else:
            merged[-1]['J'] = max(merged[-1]['J'], b)
            merged[-1]['proof_ids'].append(proof_id)
    return merged


def check_claims(claims, proofs, target):
    require(isinstance(claims, list) and bool(claims), 'claims must be nonempty')
    results = []
    for index, claim in enumerate(claims):
        require(isinstance(claim, dict), 'Each claim must be an object')
        kind = claim.get('kind')
        require(kind in ('full', 'r_gt_k', 'r_le_k'), 'Unknown claim kind')
        K, J = rational(claim['K'], 'claim.K'), rational(claim['J'], 'claim.J')
        require(K <= J, 'Reversed claim interval')
        needed = ('low', 'high') if kind == 'full' else (('high',) if kind == 'r_gt_k' else ('low',))
        coverage = []
        for case in ('I', 'II'):
            for branch in needed:
                eligible = [(Fraction(p['K']), Fraction(p['J']), p['id']) for p in proofs
                            if p['case'] == case and p['rbranch'] in ('all', branch)]
                components = merge_closed(eligible)
                cover = next((c for c in components if c['K'] <= K and c['J'] >= J), None)
                require(cover is not None,
                        f'Claim {index + 1} has a k-coverage gap for case {case}, r branch {branch}: [{K},{J}]')
                coverage.append({'case': case, 'rbranch': branch, 'K': str(cover['K']), 'J': str(cover['J']),
                                 'proof_ids': cover['proof_ids']})
        results.append({'kind': kind, 'K': str(K), 'J': str(J), 'k_endpoints': 'closed',
                        'r_scope': {'full': 'all r', 'r_gt_k': 'strict r>k', 'r_le_k': 'closed r<=k'}[kind],
                        'target': str(target), 'conclusion': 'F < target < alpha',
                        'coverage': coverage, 'III_coverage': 'inherited actual transpose into II',
                        'r_equals_k_owner': 'low or all; never high-only'})
    return results


def verify_summary(text):
    lines = [line for line in text.splitlines() if line.strip()]
    require(len(lines) == 1, 'Expected exactly one independent-verifier JSON summary')
    data = json.loads(lines[0])
    require(isinstance(data, dict) and data.get('status') == PASS, 'Independent verifier did not report Round44 PASS')
    for key in ('nodes', 'splits', 'leaves', 'open', 'max_depth', 'max_support', 'total_support'):
        require(isinstance(data.get(key), int) and not isinstance(data[key], bool) and data[key] >= 0,
                'Invalid verifier counter: ' + key)
    require(data['open'] == 0 and data['leaves'] >= 1 and data['nodes'] == 2 * data['splits'] + 1
            and data['leaves'] == data['splits'] + 1, 'Independent verifier partition counters are inconsistent')
    return data


def run_command(command, package, stdout_path, stderr_path):
    with stdout_path.open('w') as stdout, stderr_path.open('w') as stderr:
        result = subprocess.run(command, cwd=package, stdout=stdout, stderr=stderr, check=False)
    return result.returncode


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('package', nargs='?', type=Path, default=Path('.'))
    ap.add_argument('--selection', default='SELECTION.json', help='Relative to package')
    ap.add_argument('--log-dir', help='New relative package directory; must not already exist')
    ap.add_argument('--cxx', default=os.environ.get('CXX', 'c++'))
    ap.add_argument('--boost-include', type=Path)
    args = ap.parse_args()
    package = args.package.resolve(strict=True)
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '_' + str(os.getpid())
    run_dir = inside(package, args.log_dir or ('replay_logs/' + stamp), must_exist=False)
    run_dir.mkdir(parents=True, exist_ok=False)
    result = {'schema': 'rho5.cqg.round44.selected-cold-replay.v1', 'status': 'RUNNING',
              'selection': None, 'proofs': [], 'claims': [],
              'discovery_lp_used': False, 'partial_volume_used': False,
              'old_trees_replayed': False, 'p61_isolation_recomputed': False}
    summary_path = run_dir / 'REPLAY_RESULT.json'
    try:
        require(__debug__, 'Do not run with python -O: the inherited model audit uses assertions')
        result['execution'] = configure_single_cpu()
        selection_path = inside(package, args.selection)
        selection = json.loads(selection_path.read_text())
        proof_ids = selection.get('proof_ids')
        require(isinstance(proof_ids, list) and bool(proof_ids), 'proof_ids must be nonempty')
        require(all(isinstance(p, str) and re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', p) for p in proof_ids), 'Invalid proof id')
        require(len(set(proof_ids)) == len(proof_ids), 'Duplicate proof id')
        result['selection'] = relative(package, selection_path)
        result['selection_sha256'] = digest(selection_path)
        repro = inside(package, 'repro')
        for name, expected in PINNED.items():
            require(digest(inside(package, 'repro/' + name)) == expected, 'Frozen inherited asset changed: ' + name)
        documents = selection.get('analytic_documents', list(DEFAULT_DOCUMENTS))
        require(isinstance(documents, list) and bool(documents), 'analytic_documents must be nonempty')
        result['inherited_analytic_documents'] = [
            {'path': relative(package, inside(package, name)), 'sha256': digest(inside(package, name))}
            for name in documents]
        alpha = json.loads((repro / 'alpha.json').read_text())
        alpha_low = rational(alpha['isolating_interval']['lower'], 'alpha.lower')
        alpha_high = rational(alpha['isolating_interval']['upper'], 'alpha.upper')
        require(alpha_low < alpha_high, 'Reversed inherited alpha interval')
        result['alpha'] = {'path': 'repro/alpha.json', 'sha256': PINNED['alpha.json'],
                           'lower': str(alpha_low), 'upper': str(alpha_high),
                           'interval_validity': 'inherited frozen P61 isolation; not recomputed'}
        expected_kernel = (repro / 'vendor/mc_exact_kernel.hpp').read_text().replace('Big(4800)', 'Big(ROOT_DEN)')
        expected_verifier = (repro / 'vendor/mc_verify.cpp').read_text().replace('visit(', 'r44_visit_node(').replace(
            'V31_SMALL_PIVOT_GLOBAL_EXACT_PASS', PASS)
        sys.path.insert(0, str(repro))
        audit_module = importlib.import_module('verify_midband_models')
        require(Path(audit_module.__file__).resolve() == (repro / 'verify_midband_models.py').resolve(), 'Wrong model audit import')
        require(Path(sys.modules['build_midband_model'].__file__).resolve() == (repro / 'build_midband_model.py').resolve(), 'Wrong model builder import')
        if args.boost_include:
            args.boost_include = args.boost_include.expanduser().resolve(strict=True)
            require((args.boost_include / 'boost/multiprecision/cpp_int.hpp').is_file(), 'Invalid Boost include directory')
        result['compiler'] = {'program': Path(args.cxx).name, 'standard': 'c++17', 'optimization': 'O2',
                              'boost_include_supplied': bool(args.boost_include)}
        # Reject a malformed or incomplete selection before any expensive tree
        # replay. These metadata-only checks are not acceptance; every entry
        # is audited and independently verified below before claims are issued.
        preflight = []
        for proof_id in proof_ids:
            data_path = inside(package, 'proofs/' + proof_id + '/model.json')
            preflight.append(proof_metadata(proof_id, json.loads(data_path.read_text())))
        preflight_target = Fraction(preflight[0]['target'])
        require(all(Fraction(p['target']) == preflight_target for p in preflight), 'Selected proofs have different targets')
        require(preflight_target < alpha_low, 'Proof target is not below the frozen alpha lower endpoint')
        check_claims(selection.get('claims'), preflight, preflight_target)
        result['selection_metadata_preflight_passed'] = True
        metadata, target = [], None
        for proof_id in proof_ids:
            directory = inside(package, 'proofs/' + proof_id)
            for name in PROOF_FILES:
                require(inside(package, 'proofs/' + proof_id + '/' + name).is_file(), proof_id + ': missing ' + name)
            data = json.loads((directory / 'model.json').read_text())
            entry = proof_metadata(proof_id, data)
            q = Fraction(entry['target'])
            target = q if target is None else target
            require(q == target, 'Selected proofs have different contradiction targets')
            require(q < alpha_low, 'Proof target is not below the frozen alpha lower endpoint')
            if 'target' in selection:
                require(q == rational(selection['target'], 'selection.target'), 'Selection/model target mismatch')
            entry.update({'path': relative(package, directory), 'status': 'RUNNING',
                          'input_sha256': {name: digest(directory / name) for name in PROOF_FILES}})
            result['proofs'].append(entry)
            proof_log = run_dir / proof_id
            proof_log.mkdir()
            audit_log = proof_log / 'model_audit.log'
            print(json.dumps({'event': 'model_audit', 'proof_id': proof_id}), flush=True)
            with audit_log.open('w') as stream, contextlib.redirect_stdout(stream), contextlib.redirect_stderr(stream):
                audited = audit_module.audit(directory)
            require(isinstance(audited, dict) and audited.get('root_covers_analytic_necessary_root') is True
                    and audited.get('exact_header_matches_model') is True, proof_id + ': incomplete model audit result')
            require(audited.get('case') == entry['case'] and audited.get('rbranch', 'all') == entry['rbranch']
                    and audited.get('fold_i', False) == entry['fold_i']
                    and rational(audited['K'], 'audited.K') == Fraction(entry['K'])
                    and rational(audited['J'], 'audited.J') == Fraction(entry['J']),
                    proof_id + ': audited domain differs from selection metadata')
            entry['model_audit'] = audited
            entry['model_audit_log'] = relative(package, audit_log)
            # The formula/root audit alone does not authenticate the C++ code.
            require((directory / 'mc_exact_kernel.hpp').read_text() == expected_kernel, proof_id + ': exact kernel differs from frozen source')
            require((directory / 'mc_verify.cpp').read_text() == expected_verifier, proof_id + ': independent verifier differs from frozen source')
            entry['frozen_verifier_and_kernel_match'] = True
            executable = proof_log / 'mc_verify'
            compile_out, compile_err = proof_log / 'compile.stdout.log', proof_log / 'compile.stderr.log'
            command = [args.cxx, '-O2', '-std=c++17']
            if args.boost_include:
                command += ['-I', str(args.boost_include)]
            command += [relative(package, directory / 'mc_verify.cpp'), '-o', relative(package, executable)]
            print(json.dumps({'event': 'compile', 'proof_id': proof_id}), flush=True)
            code = run_command(command, package, compile_out, compile_err)
            entry['compile'] = {'returncode': code, 'stdout': relative(package, compile_out), 'stderr': relative(package, compile_err)}
            require(code == 0, proof_id + ': verifier compilation failed')
            verify_out, verify_err = proof_log / 'verify.stdout.log', proof_log / 'verify.stderr.log'
            print(json.dumps({'event': 'exact_verify', 'proof_id': proof_id}), flush=True)
            code = run_command(['./' + relative(package, executable), relative(package, directory / 'result.tree')],
                               package, verify_out, verify_err)
            entry['verify_logs'] = {'returncode': code, 'stdout': relative(package, verify_out), 'stderr': relative(package, verify_err)}
            require(code == 0, proof_id + ': independent exact verifier rejected the tree')
            entry['verification'] = verify_summary(verify_out.read_text())
            require(entry['input_sha256'] == {name: digest(directory / name) for name in PROOF_FILES},
                    proof_id + ': frozen inputs changed during replay')
            entry['status'] = 'PASS'
            metadata.append(entry)
            write_json(summary_path, result)
        result['claims'] = check_claims(selection.get('claims'), metadata, target)
        require(digest(selection_path) == result['selection_sha256'], 'Selection changed during replay')
        result['target'] = str(target)
        result['target_below_frozen_alpha_lower'] = True
        result['total_selected_nodes'] = sum(p['verification']['nodes'] for p in result['proofs'])
        result['total_selected_leaves'] = sum(p['verification']['leaves'] for p in result['proofs'])
        result['status'] = 'R44_SELECTED_NEW_PROOFS_COLD_REPLAY_PASS'
        write_json(summary_path, result)
        print(json.dumps({'status': result['status'], 'log': relative(package, summary_path),
                          'proofs': len(metadata), 'claims': len(result['claims']),
                          'nodes': result['total_selected_nodes'], 'open': 0}), flush=True)
        return 0
    except Exception as error:
        result['status'] = 'R44_SELECTED_NEW_PROOFS_COLD_REPLAY_REJECTED'
        result['error'] = str(error)
        write_json(summary_path, result)
        print(json.dumps({'status': result['status'], 'log': relative(package, summary_path), 'error': str(error)}), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
