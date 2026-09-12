"""Cheap control-flow checks with a toy interval system; no RHO5 math replay."""
from pathlib import Path
from types import SimpleNamespace, ModuleType
from fractions import Fraction
import copy
import json
import os
import tempfile
import sys

sys.setrecursionlimit(10000)
sys.dont_write_bytecode = True
import branch_worker as w
import deep_math
from fast_checkpoint import atomic_json


def leaf(kind='O'):
    return {'waves': [], 'terminal': {'kind': kind}}


def split(left, right):
    return {'waves': [], 'terminal': {'kind': 'S', 'axis': 0, 'left': left, 'right': right}}


def normal_contract(image, profile):
    lo, hi = map(Fraction, image['aux_image'][0])
    if lo > 0:
        return {'status': 'EMPTY', 'aux_image': None}
    return copy.deepcopy(image)


def checks():
    original_root = w.ROOT
    original_loader = deep_math.load_protocol
    original_verify = deep_math.verify_branch
    original_split = w._split_axis
    original_node_limit = w.MAX_TARGET_NODES
    modules = {k: sys.modules.get(k) for k in ('discovery', 'proposal')}
    names = []
    verify_calls = []
    with tempfile.TemporaryDirectory(prefix='rho5-worker-controls-') as temporary:
        root = Path(temporary).resolve()
        w.ROOT = root
        db = SimpleNamespace(common_contract=normal_contract,
                             apply_wave=lambda image, wave, **kw: image,
                             rows_and_bounds=lambda image, **kw: ([], []),
                             validate_profile=lambda profile: None)
        bp = SimpleNamespace(db=db, fs=SimpleNamespace(safe_port=lambda image: None), Q=Fraction,
                             prefix_image=lambda parent, cross_check: ({'status': 'BOUNDED', 'aux_image': [['0', '1']]}, {}))
        deep_math.load_protocol = lambda run_root: bp
        w._split_axis = lambda *args: 0
        discovery = ModuleType('discovery')
        discovery.bound_proposals = lambda *args, **kw: []
        proposal = ModuleType('proposal')
        proposal.propose_rows = lambda *args: None
        sys.modules['discovery'], sys.modules['proposal'] = discovery, proposal

        def verified(run_root, parent, base, projected, target):
            audit = deep_math.validate_branch_extension(base, projected, target)
            counts = deep_math.counts(deep_math.at(projected['tree'], target))
            closed = counts.get('O', 0) == 0
            verify_calls.append(target)
            return {'closed': closed, 'target_counts': counts, 'structural_audit': audit,
                    'status': 'TOY_CONTROL_ONLY_NOT_MATHEMATICAL_EVIDENCE'}
        deep_math.verify_branch = verified

        def task(name, tree, target):
            folder = root / name
            folder.mkdir()
            parent_path = root / (name + '_parent.json')
            base_path = root / (name + '_base.json')
            atomic_json(parent_path, {'index': 1})
            atomic_json(base_path, {'profile': 'PIVOT_CYCLE', 'tree': tree})
            atomic_json(folder / 'TASK.json', {'task_id': name, 'index': 1, 'target_path': target,
                        'parent_file': parent_path.name, 'base_file': base_path.name,
                        'input_sha256': w.file_sha(base_path), 'parent_sha256': w.file_sha(parent_path)})
            return folder

        try:
            assert w.path_is_owned('010', '') and w.path_is_owned('010', '01')
            assert w.path_is_owned('010', '010111') and not w.path_is_owned('010', '011')
            names.append('target_prefix_ownership')

            # A single process walks one open ray to 500 and closes all its siblings.
            folder = task('depth500', split(split(leaf(), leaf('I')), leaf('I')), '00')
            before = len(verify_calls)
            worker = w.BranchWorker(folder)
            worker.run()
            result = w.read_json(folder / 'RESULT.json')
            milestone = w.read_json(folder / 'DEPTH300.json')
            final = w.read_json(folder / 'final.json')
            mark = w.read_json(folder / 'depth300_certificate.json')
            assert result['status'] == 'DEPTH500_OPEN' and not result['closed']
            assert result['maxdepth'] == 500 and result['target_counts']['O'] == 1
            assert len(verify_calls) == before + 1
            assert milestone['pid'] == os.getpid() == result['pid']
            assert milestone['same_process_continues'] and not milestone['search_restarted']
            assert deep_math.counts(mark['tree'])['maxdepth'] == 300
            assert w.file_sha(folder / 'depth300_certificate.json') == milestone['checkpoint_sha256']
            assert deep_math.at(final['tree'], '1') == leaf()
            assert deep_math.at(final['tree'], '01') == leaf()
            names.append('500_continuous_and_300_immutable_same_pid_one_final_check')

            # A latest paid input may have already split the originally assigned root.
            folder = task('partial_base', split(split(leaf(), leaf('I')), leaf('I')), '0')
            def close_small(image, profile):
                lo, hi = map(Fraction, image['aux_image'][0])
                return {'status': 'EMPTY', 'aux_image': None} if hi <= Fraction(1, 4) else copy.deepcopy(image)
            db.common_contract = close_small
            worker = w.BranchWorker(folder)
            worker.run()
            result = w.read_json(folder / 'RESULT.json')
            assert result['status'] == 'CLOSED' and result['closed']
            assert result['target_counts'].get('O', 0) == 0
            assert deep_math.at(w.read_json(folder / 'final.json')['tree'], '01') == leaf('I')
            names.append('continue_partial_latest_target_and_preserve_paid_sibling')
            db.common_contract = normal_contract

            # STOP returns with an explicit unverified checkpoint and no exact replay.
            folder = task('stopped', split(leaf(), leaf('I')), '0')
            atomic_json(folder / 'STOP.json', {'stop': True})
            before = len(verify_calls)
            w.BranchWorker(folder).run()
            assert not (folder / 'RESULT.json').exists()
            assert w.read_json(folder / 'STOPPED.json')['status'] == 'SAVED_UNVERIFIED_STOP'
            assert len(verify_calls) == before and (folder / 'final.json').exists()
            names.append('stop_saves_without_verification_or_closed_credit')

            # Resume exactly that saved projection; no artificial new timing budget.
            (folder / 'STOP.json').unlink()
            db.common_contract = lambda image, profile: {'status': 'EMPTY', 'aux_image': None} if Fraction(image['aux_image'][0][1]) <= Fraction(1, 2) else copy.deepcopy(image)
            resumed = w.BranchWorker(folder)
            assert resumed.resumed
            resumed.run()
            assert w.read_json(folder / 'RESULT.json')['closed']
            assert w.read_json(folder / 'START.json')['resumed']
            names.append('resume_saved_projection_without_initial_math_replay')
            db.common_contract = normal_contract

            # Resource guard retains the most recent legal tree and verifies it once.
            folder = task('node_cap', split(leaf(), leaf('I')), '0')
            w.MAX_TARGET_NODES = 3
            before = len(verify_calls)
            w.BranchWorker(folder).run()
            result = w.read_json(folder / 'RESULT.json')
            assert result['status'] == 'RESOURCE_PAUSED' and not result['closed']
            assert result['target_counts']['nodes'] == 3 and len(verify_calls) == before + 1
            names.append('node_guard_is_terminal_pause_with_saved_evidence')
            w.MAX_TARGET_NODES = original_node_limit

            # A rejected wave never enters the recorded certificate.
            folder = task('bad_wave', split(leaf(), leaf('I')), '0')
            discovery.bound_proposals = lambda *args, **kw: [{'bad': 1}]
            def reject(*args, **kw):
                raise ValueError('TOY_REJECTED_WAVE')
            db.apply_wave = reject
            before = len(verify_calls)
            try:
                w.BranchWorker(folder).run()
            except ValueError as exc:
                assert str(exc) == 'TOY_REJECTED_WAVE'
            else:
                raise AssertionError('Rejected wave was retained')
            assert deep_math.at(w.read_json(folder / 'final.json')['tree'], '0')['waves'] == []
            assert not (folder / 'RESULT.json').exists() and len(verify_calls) == before
            names.append('rejected_wave_never_saved')

            # Oversize writes leave the old durable checkpoint byte-for-byte intact.
            checkpoint = root / 'size_guard.json'
            atomic_json(checkpoint, {'old': True})
            old_sha = w.file_sha(checkpoint)
            try:
                atomic_json(checkpoint, {'oversize': 'x' * 1000}, max_bytes=20)
            except ValueError as exc:
                assert 'CHECKPOINT_TOO_LARGE' in str(exc)
            else:
                raise AssertionError('Size guard did not reject')
            assert w.file_sha(checkpoint) == old_sha
            names.append('checkpoint_size_guard_preserves_previous_bytes')
        finally:
            w.ROOT, w._split_axis, w.MAX_TARGET_NODES = original_root, original_split, original_node_limit
            deep_math.load_protocol, deep_math.verify_branch = original_loader, original_verify
            for key, value in modules.items():
                if value is None:
                    sys.modules.pop(key, None)
                else:
                    sys.modules[key] = value
    return {'status': 'PASS', 'checks': names, 'count': len(names),
            'rho5_mathematical_replay': False, 'synthetic_control_system_only': True}


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
