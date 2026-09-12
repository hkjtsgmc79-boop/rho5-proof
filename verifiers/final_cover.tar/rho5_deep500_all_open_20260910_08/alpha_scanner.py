"""One bounded, source-bound alpha discovery pass; original search is untouched.

No LP or split/wave discovery is performed. Only a separately persisted cut and
alpha_cover.verify_cut receipt may enter REGISTRY.json. Run on X explicitly.
"""
from pathlib import Path
from fractions import Fraction
from collections import Counter, OrderedDict
import argparse
import copy
import fcntl
import hashlib
import json
import os
import signal
import sys
import tempfile
import time
import traceback

sys.setrecursionlimit(10000)
sys.dont_write_bytecode = True
for _name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[_name] = '1'

DEFAULT_ROOT = Path('/root/microscope_ws/rho5_deep500_all_open_20260910_08')
PARENTS = (338726, 435003, 563285, 675104)
S0 = '338726_e30b92483560870aa201'


class BudgetExpired(Exception):
    pass


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False) + '\n').encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def atomic_bytes(path, raw):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix=path.name + '.', suffix='.tmp', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(name, path)
    finally:
        if os.path.exists(name):
            os.unlink(name)


def atomic(path, value):
    atomic_bytes(path, encoded(value))


def stable_bytes(path):
    """An atomic replacement cannot change the opened inode we are reading."""
    for _ in range(3):
        with Path(path).open('rb') as stream:
            before = os.fstat(stream.fileno())
            raw = stream.read()
            after = os.fstat(stream.fileno())
        if (before.st_ino, before.st_size, before.st_mtime_ns) == (after.st_ino, after.st_size, after.st_mtime_ns) and len(raw) == after.st_size:
            return raw, {'inode': after.st_ino, 'mtime_ns': after.st_mtime_ns, 'bytes': len(raw)}
    raise ValueError('Source changed in place while reading: ' + str(path))


def read(path):
    return json.loads(stable_bytes(path)[0])


def same_counts(left, right):
    return all(left.get(k, 0) == right.get(k, 0) for k in set(left) | set(right))


class Scanner:
    def __init__(self, args):
        self.root = args.root.resolve()
        if not str(self.root).startswith('/root/microscope_ws/') or not Path('/proc/self/stat').exists():
            raise RuntimeError('This scanner runs only in the authorized X task workspace')
        self.b14 = args.b14_dir.resolve()
        self.out = self.root / 'alpha_v1'
        self.out.mkdir(exist_ok=True)
        self.lock = (self.out / 'SCANNER.lock').open('a+')
        fcntl.flock(self.lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        self.run_id = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime()) + '_' + str(os.getpid())
        self.run_dir = self.out / 'runs' / self.run_id
        self.run_dir.mkdir(parents=True)
        self.started = time.monotonic()
        self.started_cpu = time.process_time()
        self.budget = min(float(args.seconds), 1200.0)
        if self.budget <= 0:
            raise ValueError('Positive budget required')
        self.source = Path(read(self.root / 'CONFIG.json')['source_root']).resolve()
        sys.path.insert(0, str(self.root))
        import deep_math
        import alpha_cover
        self.dm, self.ac = deep_math, alpha_cover
        self.bp = deep_math.load_protocol(self.root)
        self.alpha_identity = alpha_cover.configure(self.b14)
        self.centers = alpha_cover.fixed_centers()
        self.manifest = read(self.root / 'runtime/DEEP500_MANIFEST.json')
        # These caches never mix discovery boxes with verifier-sealed results.
        self.discovery_prefix = {}
        self.discovery_nodes = OrderedDict()
        self.discovery_ports = OrderedDict()
        self.verifier_cache = {}
        self.counter = Counter()
        self.diag_counts = Counter()
        self.current = None
        self.current_certificate = None
        self.current_reduced = None
        self.last_progress = 0.0
        reg = self.out / 'REGISTRY.json'
        self.registry = read(reg) if reg.exists() else {'schema': 'RHO5_ALPHA_REGISTRY_V1', 'accepted': {}, 'scans': [], 'errors': []}
        if self.registry.get('schema') != 'RHO5_ALPHA_REGISTRY_V1' or not isinstance(self.registry.get('accepted'), dict):
            raise ValueError('Registry schema differs; refusing to overwrite it')
        atomic(self.run_dir / 'CONFIG.json', {'root': str(self.root), 'b14_dir': str(self.b14), 'budget_seconds': self.budget,
            'started_epoch': time.time(), 'alpha_identity': self.alpha_identity, 'scanner_file_sha256': sha(Path(__file__).read_bytes()),
            'new_lp_calls': 0, 'new_waves': 0, 'new_splits': 0, 'production_workers_modified': False})

    def relative(self, path):
        return str(Path(path).resolve().relative_to(self.root))

    def owned(self, path, root=None):
        root = self.root if root is None else Path(root).resolve()
        p = (root / path).resolve()
        if not p.is_relative_to(root):
            raise ValueError('Source path escaped task root')
        return p

    def event(self, kind, **fields):
        with (self.run_dir / 'EVENTS.jsonl').open('a') as stream:
            stream.write(json.dumps({'epoch': time.time(), 'event': kind, **fields}, sort_keys=True) + '\n')
            stream.flush()

    def save_registry(self):
        self.registry['updated_epoch'] = time.time()
        self.registry['latest_run'] = self.relative(self.run_dir)
        atomic(self.out / 'REGISTRY.json', self.registry)

    def progress(self, phase='SCANNING', force=False):
        if not force and time.monotonic() - self.last_progress < 5:
            return
        value = {'epoch': time.time(), 'pid': os.getpid(), 'run_id': self.run_id, 'phase': phase,
            'elapsed_seconds': time.monotonic() - self.started, 'budget_seconds': self.budget,
            'cpu_seconds': time.process_time() - self.started_cpu,
            'counters': dict(self.counter), 'accepted_total': len(self.registry['accepted']), 'current_source': self.current,
            'mathematical_discovery_is_not_acceptance': True, 'model_wakeups': False}
        atomic(self.out / 'SCANNER_STATUS.json', value)
        self.last_progress = time.monotonic()

    def safe_point(self):
        self.progress()
        if time.monotonic() - self.started >= self.budget:
            raise BudgetExpired('Fixed scanner wall budget exhausted; search remains running')
        if (self.out / 'STOP_SCANNER.json').exists():
            raise BudgetExpired('Explicit scanner-only stop')

    def pin(self, path, label, expected=None):
        raw, stat = stable_bytes(path)
        identity = sha(raw)
        if expected and identity != expected:
            raise ValueError('Completed source raw hash mismatch: ' + str(path))
        dest = self.out / 'sources' / (identity + '_' + label)
        if dest.exists():
            if sha(dest.read_bytes()) != identity:
                raise ValueError('Previously pinned source bytes changed')
        else:
            atomic_bytes(dest, raw)
        return dest, json.loads(raw), {'source_path': str(path), 'source_file': self.relative(dest),
            'source_file_sha256': identity, 'captured_epoch': time.time(), **stat}

    def envelope(self, parent, cert):
        if cert.get('rule') == self.dm.OLD_RULE:
            self.dm.validate_legacy_binding(parent, cert, self.manifest['legacy_rule_identity'], self.bp)
            return self.bp.wrap(parent, cert['tree'], cert['profile'])
        expect = self.bp.binding(parent)
        if set(cert) != set(expect) | {'tree', 'profile'} or any(cert[k] != value for k, value in expect.items()):
            raise ValueError('Deep source parent/protocol binding mismatch')
        self.bp.db.validate_profile(cert['profile'])
        self.dm.counts(cert['tree'])
        return cert

    def lineage(self, tree, path, final_waves=True):
        result, node = [], tree
        for depth in range(len(path) + 1):
            if depth == len(path):
                result.append({'waves': node['waves'] if final_waves else []})
                return result
            term = node['terminal']
            if term.get('kind') != 'S':
                raise ValueError('Projection does not contain requested target path')
            result.append({'waves': node['waves'], 'axis': term['axis']})
            node = term['left' if path[depth] == '0' else 'right']

    def accept(self, parent_path, profile, path, lineage, terminal, source):
        self.safe_point()
        cert = self.ac.make_cut(self.bp, parent_path, profile, path, lineage, terminal)
        raw = encoded(cert)
        identity = sha(raw)
        if identity in self.registry['accepted']:
            previous = self.registry['accepted'][identity]
            if (sha(self.owned(previous['cut_certificate_file']).read_bytes()) != identity
                    or sha(self.owned(previous['acceptance_file']).read_bytes()) != previous['acceptance_sha256']):
                raise ValueError('Previously accepted cut/receipt bytes changed')
            self.counter['accepted_cut_reused'] += 1
            return previous
        cert_path = self.out / 'certificates' / (identity + '.json')
        receipt_path = self.out / 'receipts' / (identity + '.json')
        atomic_bytes(cert_path, raw)
        self.counter['independent_acceptance_attempts'] += 1
        receipt = self.ac.verify_cut(self.bp, parent_path, cert_path, self.centers, self.verifier_cache)
        if receipt.get('mathematical_acceptance') is not True or receipt.get('certificate_sha256') != identity:
            raise ValueError('Independent acceptance did not bind the persisted cut bytes')
        if receipt.get('parent_raw_sha256') != sha(parent_path.read_bytes()) or receipt.get('cut_path') != path:
            raise ValueError('Independent acceptance source identity mismatch')
        atomic(receipt_path, receipt)
        row = {'index': int(receipt['parent_index']), 'cut_path': path, 'parent_file': self.relative(parent_path),
            'parent_file_sha256': receipt['parent_raw_sha256'], 'cut_certificate_file': self.relative(cert_path),
            'cut_certificate_sha256': identity, 'acceptance_file': self.relative(receipt_path),
            'acceptance_sha256': sha(receipt_path.read_bytes()), 'source_file': source['source_file'],
            'source_file_sha256': source['source_file_sha256'], 'terminal_kind': terminal['kind'],
            'accepted_epoch': time.time(), 'run_id': self.run_id, 'source_kind': source['kind'],
            'source_task_id': source.get('task_id'), 'whole_original_parent_claimed': False}
        self.registry['accepted'][identity] = row
        self.counter['new_independently_accepted_cuts'] += 1
        self.save_registry()
        self.event('CUT_ACCEPTED', **row)
        self.progress(force=True)
        return row

    def import_s0(self):
        starter = read(self.b14 / 'input/STARTER_CASES.json')['cases'][0]
        proposal = read(self.b14 / 'ALPHA_PROPOSALS.json')[0]
        if starter['index'] != 338726 or starter['path'] != '010110101100000001010011':
            raise ValueError('B14 starter zero identity changed')
        parent_path, parent, _ = self.pin(self.b14 / 'data/production/cases/338726/parent.json', 'S0_parent.json', proposal['source']['parent_raw_sha256'])
        _, cert, source = self.pin(self.owned(starter['projection_file'], self.b14 / 'data'), 'S0_projection.json', starter['projection_raw_sha256'])
        if proposal['source']['projection_sha256'] != source['source_file_sha256'] or proposal['source']['path'] != starter['path']:
            raise ValueError('B14 S0 proposal/projection differs')
        cert = self.envelope(parent, cert)
        port = proposal['port']
        # Translate only the port envelope; all original rational claims are
        # reconstructed and independently checked by the new pinned acceptor.
        port = {'rule': self.ac.PORT_RULE, 'semantic': 'ALPHA_SAFE', 'method': 'B14_SORTED_R',
            'centers_sha256': port['centers_sha256'], 'representation': port['representation'], 'branches': port['branches']}
        source.update(kind='B14_S0_SOURCE_PROJECTION', index=338726, task_id=S0)
        self.current = source
        self.accept(parent_path, cert['profile'], starter['path'], self.lineage(cert['tree'], starter['path']),
            {'kind': 'ALPHA_SAFE', 'port': port}, source)
        self.event('S0_IMPORTED_WITH_INDEPENDENT_RECEIPT')

    def production_source(self, index):
        row = read(self.source / 'STATE.json')['cases'][str(index)]
        pp, parent, _ = self.pin(self.owned(row['parent'], self.source), str(index) + '_parent.json', row['parent_sha256'])
        cp, cert, meta = self.pin(self.owned(row['certificate'], self.source), str(index) + '_production.json', row['certificate_sha256'])
        rp, result, _ = self.pin(self.owned(row['last_result'], self.source), str(index) + '_completed_receipt.json')
        if parent['index'] != index or result['index'] != index:
            raise ValueError('Completed production parent/result index mismatch')
        if result['certificate_sha256'] != row['certificate_sha256'] or result['parent_sha256'] != row['parent_sha256']:
            raise ValueError('Completed production receipt byte identity mismatch')
        check = self.dm.validate_legacy_binding(parent, cert, self.manifest['legacy_rule_identity'], self.bp)
        counts = check['counts']
        receipt = result['exact_receipt']
        if not all(same_counts(counts, c) for c in (row['counts'], result['counts'], receipt['counts'])):
            raise ValueError('Completed production receipt count mismatch')
        expected = 'OPEN' if counts.get('O', 0) else 'SAFE' if counts.get('A', 0) or counts.get('H', 0) else 'EMPTY'
        if result['status'] != expected or receipt['status'] != expected or receipt['index'] != index or result['complete'] != (not counts.get('O', 0)):
            raise ValueError('Missing or inconsistent completed exact receipt')
        meta.update(kind='LATEST_COMPLETED_PRODUCTION', index=index, parent_file=self.relative(pp),
            parent_file_sha256=row['parent_sha256'], completed_receipt_file=self.relative(rp),
            completed_receipt_sha256=sha(rp.read_bytes()), source_completed_epoch=row.get('completed_epoch'), target_path='')
        return pp, parent, self.bp.wrap(parent, cert['tree'], cert['profile']), meta

    def running_source(self, task):
        folder = self.owned(task['folder'])
        tp, task_spec, _ = self.pin(folder / 'TASK.json', task['task_id'] + '_TASK.json')
        if task_spec['task_id'] != task['task_id'] or task_spec['target_path'] != task['target_path']:
            raise ValueError('Running task ownership metadata changed')
        pp, parent, _ = self.pin(self.owned(task_spec['parent_file']), str(task['index']) + '_parent.json', task_spec['parent_sha256'])
        _, cert, meta = self.pin(folder / 'final.json', task['task_id'] + '_checkpoint.json')
        # The saved checkpoint remains an untrusted discovery source. Its
        # descendant C/H/A/I/N nodes receive credit only inside verify_cut.
        cert = self.envelope(parent, cert)
        self.dm.at(cert['tree'], task['target_path'])
        meta.update(kind='LATEST_ATOMIC_RUNNING_CHECKPOINT', index=int(task['index']), task_id=task['task_id'],
            target_path=task['target_path'], parent_file=self.relative(pp), parent_file_sha256=task_spec['parent_sha256'],
            task_file=self.relative(tp), original_input_sha256=task_spec['input_sha256'],
            current_checkpoint_is_not_paid_mathematical_acceptance=True)
        return pp, parent, cert, meta

    def cache(self, cache, key, compute):
        if key in cache:
            cache.move_to_end(key)
            return cache[key]
        value = compute()
        cache[key] = value
        if len(cache) > 8192:
            cache.popitem(last=False)
        return value

    def propagate(self, inbox, waves, profile):
        key = self.ac.digest({'inbox': inbox, 'waves': waves, 'profile': profile})
        def calculate():
            self.counter['discovery_unique_node_replays'] += 1
            out = self.bp.db.common_contract(copy.deepcopy(inbox), profile=profile)
            for wave in waves:
                self.safe_point()
                out = self.bp.db.apply_wave(out, wave, profile=profile, cross_check=False)
            return out
        return self.cache(self.discovery_nodes, key, calculate)

    def port(self, aux):
        key = self.ac.digest(aux)
        def calculate():
            self.counter['discovery_port_calls'] += 1
            return self.ac.discover_port(aux, self.centers)
        return self.cache(self.discovery_ports, key, calculate)

    def split(self, out, axis, bit):
        boxes = copy.deepcopy(out['aux_image'])
        lo, hi = map(Fraction, boxes[axis])
        mid = (lo + hi) / 2
        if not lo < mid < hi:
            raise ValueError('Degenerate source split')
        boxes[axis][1 if bit == '0' else 0] = str(mid)
        return {'status': 'BOUNDED', 'aux_image': boxes}

    def diagnostic(self, parent_path, cert, path, out, source):
        # A few full current sources per parent, rather than repeating the
        # expensive 32-representation failure audit for every visited node.
        index = source['index']
        key = (index, source['source_file_sha256'])
        if self.diag_counts[key] >= 2:
            return
        self.diag_counts[key] += 1
        candidates = []
        ac = self.ac
        x = ac._image(out['aux_image'])
        tl = ac._math().modules['transport_local']
        for name in ac._representation_names():
            self.safe_point()
            try:
                y = ac._representation(x, name)
                best = min(ac._v36_scores(y, self.centers), key=lambda r: r['budget'])
                candidates.append({'method': 'V36_FULL_GAP', 'representation': name,
                    'budget': str(best['budget']), 'threshold': str(ac.V36_RADIUS), 'center': best['center']})
                branches = []
                for tag, z in tl.sorted_branches(y):
                    target, loss, _ = tl.sorted_R(z)
                    scores = [max(max(abs(v.lo - a), abs(v.hi - a)) for v, a in zip(target, center[:22])) + tl.KAPPA[j] * loss.hi for j, center in enumerate(self.centers)]
                    j = min(range(4), key=lambda k: scores[k])
                    branches.append({'branch': tag, 'center': j, 'budget': str(scores[j]), 'loss_upper': str(loss.hi)})
                candidates.append({'method': 'B14_SORTED_R', 'representation': name,
                    'budget': str(max(Fraction(b['budget']) for b in branches)), 'threshold': str(ac.R_RADIUS), 'branches': branches})
            except (ValueError, ZeroDivisionError):
                continue
        bests = {method: min([r for r in candidates if r['method'] == method], key=lambda r: Fraction(r['budget']), default=None)
                 for method in ('V36_FULL_GAP', 'B14_SORTED_R')}
        projection = {k: v for k, v in cert.items() if k != 'tree'}
        projection['tree'] = self.dm.project(cert['tree'], path)
        name = str(index) + '_' + sha((source['source_file_sha256'] + path).encode())[:24]
        dest = self.out / 'diagnostics' / self.run_id / (name + '_projection.json')
        atomic(dest, projection)
        atomic(dest.with_name(name + '_diagnostic.json'), {'status': 'CURRENT_SOURCE_ALPHA_PORT_UNPAID',
            'epoch': time.time(), 'index': index, 'path': path, 'parent_file': self.relative(parent_path),
            'parent_file_sha256': sha(parent_path.read_bytes()), 'projection_file': self.relative(dest),
            'projection_file_sha256': sha(dest.read_bytes()), 'source': source,
            'aux_image': out['aux_image'], 'aux_image_sha256': ac.digest(out['aux_image']), 'best_failed_metrics': bests,
            'mathematical_acceptance': False, 'outside_siblings': 'O', 'ancestor_waves_and_axes': 'EXACT_SOURCE_COPY'})
        self.counter['failure_projections_saved'] += 1

    def scan(self, parent_path, parent, cert, source):
        self.current = source
        self.current_certificate = cert
        self.current_reduced = cert
        self.progress(force=True)
        atomic(self.run_dir / ('SOURCE_' + str(self.counter['sources_started']) + '.json'), source)
        self.counter['sources_started'] += 1
        profile, target = cert['profile'], source.get('target_path', '')
        parent_identity = sha(parent_path.read_bytes())
        if parent_identity not in self.discovery_prefix:
            self.discovery_prefix[parent_identity] = self.bp.prefix_image(parent, cross_check=False)[0]
        prefix = self.discovery_prefix[parent_identity]
        open_cache = {}
        def has_open(node):
            key = id(node)
            if key not in open_cache:
                term = node['terminal']
                open_cache[key] = term['kind'] == 'O' or (term['kind'] == 'S' and (has_open(term['left']) or has_open(term['right'])))
            return open_cache[key]
        def visit(node, inbox, path, ancestry):
            self.safe_point()
            if not (target.startswith(path) or path.startswith(target)):
                return node
            if not has_open(node):
                self.counter['paid_subtrees_retained_without_replay'] += 1
                return node
            out = self.propagate(inbox, node['waves'], profile)
            lineage = ancestry + [{'waves': node['waves']}]
            terminal = None
            if out['status'] == 'EMPTY':
                terminal = {'kind': 'EMPTY_INTERVAL'}
                replacement = {'kind': 'I'}
            elif out['status'] == 'BOUNDED':
                port = self.port(out['aux_image'])
                if port is not None:
                    terminal = {'kind': 'ALPHA_SAFE', 'port': port}
                    replacement = {'kind': 'N', 'port': port}
            else:
                raise ValueError('Unknown exact discovery image status')
            if terminal is not None:
                self.accept(parent_path, profile, path, lineage, terminal, source)
                self.counter['subtrees_pruned_by_independent_cut'] += 1
                return {'waves': node['waves'], 'terminal': replacement}
            term = node['terminal']
            if term['kind'] == 'O':
                self.counter['open_leaves_not_closed'] += 1
                self.diagnostic(parent_path, cert, path, out, source)
                return node
            if term['kind'] != 'S':
                return node
            ancestors = ancestry + [{'waves': node['waves'], 'axis': term['axis']}]
            for bit, side in [('0', 'left'), ('1', 'right')]:
                if target.startswith(path + bit) or (path + bit).startswith(target):
                    term[side] = visit(term[side], self.split(out, term['axis'], bit), path + bit, ancestors)
            return node
        cert['tree'] = visit(cert['tree'], prefix, '', [])
        # Parent projections may have been pruned above the owned task. Such an
        # accepted ancestor already closes that task through coverage_binding.
        if source['kind'] == 'LATEST_ATOMIC_RUNNING_CHECKPOINT':
            try:
                subtree = self.dm.at(cert['tree'], target)
            except ValueError:
                subtree = None
            def reduced_open(n):
                t = n['terminal']
                return t['kind'] == 'O' or (t['kind'] == 'S' and (reduced_open(t['left']) or reduced_open(t['right'])))
            if subtree is not None and not reduced_open(subtree):
                self.accept(parent_path, profile, target, self.lineage(cert['tree'], target, final_waves=False),
                    {'kind': 'EXACT_SUBTREE', 'tree': subtree}, source)
        self.save_partial('SOURCE_SCAN_COMPLETED')
        self.registry['scans'].append({'run_id': self.run_id, 'source': source, 'completed_epoch': time.time(),
            'discovery_reduction_is_not_whole_parent_acceptance': True})
        self.save_registry()
        self.counter['sources_completed'] += 1
        self.current_certificate = None
        self.current_reduced = None

    def save_partial(self, reason):
        if self.current_reduced is None or self.current is None:
            return
        identity = self.current['source_file_sha256']
        path = self.out / 'partial' / self.run_id / (identity + '.json')
        atomic(path, {'schema': 'RHO5_ALPHA_REDUCED_DISCOVERY_TREE_V1', 'status': reason,
            'source': self.current, 'certificate': self.current_reduced,
            'mathematical_acceptance': False, 'new_terminal_kind': 'N', 'unchanged_old_waves_and_splits': True,
            'each_published_cut_independently_accepted': True, 'epoch': time.time()})
        self.event('PARTIAL_SAVED', file=self.relative(path), reason=reason)

    def failed_source(self, label):
        error = {'epoch': time.time(), 'run_id': self.run_id, 'source': self.current, 'label': label, 'traceback': traceback.format_exc()}
        self.registry['errors'].append(error)
        self.save_registry()
        self.event('SOURCE_ERROR', **error)
        atomic(self.run_dir / ('ERROR_' + str(len(self.registry['errors'])) + '.json'), error)

    def run(self):
        def expired(signum, frame):
            raise BudgetExpired('Scanner-only signal or hard 20-minute wall budget')
        old_handlers = {s: signal.signal(s, expired) for s in (signal.SIGALRM, signal.SIGTERM, signal.SIGINT)}
        signal.setitimer(signal.ITIMER_REAL, self.budget)
        phase = 'COMPLETED'
        try:
            self.progress('IMPORTING_S0', force=True)
            self.import_s0()
            for index in PARENTS:
                self.safe_point()
                self.current = {'kind': 'PRODUCTION_SOURCE_SNAPSHOT', 'index': index}
                self.current_reduced = None
                try:
                    self.scan(*self.production_source(index))
                except BudgetExpired:
                    raise
                except Exception:
                    self.failed_source('PRODUCTION_' + str(index))
            running = [r for r in read(self.root / 'RUN_STATE.json')['tasks'].values()
                       if r.get('status') == 'RUNNING' and int(r['index']) in PARENTS]
            # Balance parents; newest source is captured only as it is visited.
            groups = {i: sorted([r for r in running if int(r['index']) == i], key=lambda r: r['task_id']) for i in PARENTS}
            for offset in range(max([len(v) for v in groups.values()] + [0])):
                for index in PARENTS:
                    if offset >= len(groups[index]):
                        continue
                    task = groups[index][offset]
                    self.safe_point()
                    self.current = {'kind': 'RUNNING_SOURCE_SNAPSHOT', 'index': index, 'task_id': task['task_id']}
                    self.current_reduced = None
                    try:
                        self.scan(*self.running_source(task))
                    except BudgetExpired:
                        raise
                    except Exception:
                        self.failed_source('RUNNING_' + task['task_id'])
        except BudgetExpired as exc:
            phase = 'BUDGET_EXHAUSTED_CHECKPOINTS_PRESERVED'
            self.event('SCANNER_BUDGET_STOP', reason=str(exc))
        except BaseException:
            phase = 'ERROR_SAVED'
            self.failed_source('SCANNER')
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            for sig, handler in old_handlers.items():
                signal.signal(sig, handler)
            self.save_partial(phase)
            self.save_registry()
            self.progress(phase, force=True)
            self.event('SCANNER_FINISHED', phase=phase, counters=dict(self.counter))
        return 0 if phase != 'ERROR_SAVED' else 2


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=DEFAULT_ROOT)
    parser.add_argument('--b14-dir', type=Path, required=True)
    parser.add_argument('--seconds', type=float, default=1200)
    args = parser.parse_args()
    os.nice(max(0, 10 - os.getpriority(os.PRIO_PROCESS, 0)))
    scanner = Scanner(args)
    return scanner.run()


if __name__ == '__main__':
    raise SystemExit(main())
