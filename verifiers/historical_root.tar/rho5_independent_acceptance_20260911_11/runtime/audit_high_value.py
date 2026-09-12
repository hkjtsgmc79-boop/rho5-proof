#!/usr/bin/env python3
"""Bounded diagnostics on an immutable accepted B17 tree; adds no proof credit."""
from pathlib import Path
from collections import Counter
import argparse, cProfile, gzip, hashlib, io, json, os, pstats, statistics, sys, time

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--package', type=Path, required=True)
    parser.add_argument('--tree', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--samples', type=int, default=32)
    parser.add_argument('--native', action='store_true')
    args = parser.parse_args()
    if os.getpriority(os.PRIO_PROCESS, 0) < 10:
        os.setpriority(os.PRIO_PROCESS, 0, 10)
    for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
        os.environ[key] = '1'
    sys.path.insert(0, str(args.package.resolve()))
    from tree_protocol import root_box, halve
    from interval_capacity import oracle, ALPHA, CENTERS
    from relaxation import propose, N, FI, NAMES
    if args.native:
        from native_backend import oracle as native_oracle, propose, ENCLOSURE
        def oracle(box):return native_oracle(box,enclosure=ENCLOSURE)
    from capacity import FRAME_NAMES
    data = json.loads(args.tree.read_text())
    assert data['task'] is None and data['root_path'] == ''
    assert data['model_sha256'] == sha(args.package / 'models/B17_FULL.json')
    args.out.mkdir()
    stack = [(root_box(), '')]
    kinds, e_reasons, open_reasons, depths, signs = (Counter() for _ in range(5))
    frontiers = []
    start = time.monotonic()
    with gzip.open(args.out / 'OPEN_FRONTIERS.jsonl.gz', 'wt') as gz:
        for index, node in enumerate(data['nodes']):
            box, route = stack.pop()
            kind = node['kind']; kinds[kind] += 1
            if kind == 'S':
                left, right = halve(box, node['axis'])
                stack.extend([(right, route + '1'), (left, route + '0')])
                continue
            if kind != 'O':
                continue
            result = oracle(box)
            reason = result.get('reason', result.get('port', 'OPEN'))
            if kind == 'E':
                e_reasons[result['status'] + ':' + reason] += 1
                continue
            depths[len(route)] += 1
            open_reasons[result['status'] + ':' + reason] += 1
            rec = {'index': index, 'path': route, 'depth': len(route), 'box': [v.data() for v in box],
                   'oracle': result}
            if result['status'] == 'OPEN':
                for i in range(5, 14):
                    if box[i].lo <= 0 <= box[i].hi and box[i].lo != box[i].hi:
                        signs[FRAME_NAMES[i]] += 1
            frontiers.append((box, rec))
            gz.write(json.dumps(rec) + '\n')
    assert not stack
    oracle_seconds = time.monotonic() - start
    selected = [frontiers[i * len(frontiers) // min(args.samples, len(frontiers))]
                for i in range(min(args.samples, len(frontiers)))] if frontiers else []
    import scipy.optimize
    original_lp = scipy.optimize.linprog
    lp_records = []
    current = {}
    def timed_lp(c, *pos, **kw):
        started = time.monotonic()
        result = original_lp(c, *pos, **kw)
        kind = 'phase' if len(c) == N + 1 else 'height'
        rec = {'sample': current['sample'], 'kind': kind, 'seconds': time.monotonic() - started,
               'status': int(result.status), 'success': bool(result.success),
               'fun': float(result.fun) if result.fun is not None else None}
        if kind == 'height' and result.success:
            rec['numeric_height_upper'] = current['F_center'] - float(result.fun)
        lp_records.append(rec)
        return result
    scipy.optimize.linprog = timed_lp
    controls = []
    prof = cProfile.Profile()
    prof.enable()
    started = time.monotonic()
    for n, (box, rec) in enumerate(selected):
        aux = rec['oracle'].get('aux_image')
        from fractions import Fraction
        current.update(sample=n, F_center=float((Fraction(aux[FI][0])+Fraction(aux[FI][1]))/2) if aux else None)
        before = time.monotonic()
        candidate = propose(box)
        controls.append({'sample': n, 'path': rec['path'], 'box': rec['box'],
                         'oracle': rec['oracle'], 'certificate': candidate,
                         'seconds': time.monotonic() - before})
    seconds = time.monotonic() - started
    prof.disable()
    scipy.optimize.linprog = original_lp
    profile_text = io.StringIO()
    pstats.Stats(prof, stream=profile_text).sort_stats('cumulative').print_stats(30)
    (args.out / 'PROFILE.txt').write_text(profile_text.getvalue())
    prof.dump_stats(str(args.out / 'PROFILE.pstats'))
    (args.out / 'SAMPLE_CONTROLS.json').write_text(json.dumps(controls, indent=2) + '\n')
    (args.out / 'LP_DIAGNOSTICS.json').write_text(json.dumps(lp_records, indent=2) + '\n')
    open_images = [rec['oracle'] for _, rec in frontiers if rec['oracle']['status'] == 'OPEN']
    widths = {}
    from fractions import Fraction as Q
    for name in ('p', 'e', 'beta', 'r', 's', 't', 'F'):
        i = NAMES.index(name)
        vals = [float(Q(rec['aux_image'][i][1])-Q(rec['aux_image'][i][0])) for rec in open_images]
        if vals:
            widths[name] = {'min': min(vals), 'median': statistics.median(vals), 'max': max(vals)}
    height_lps = [v for v in lp_records if v['kind']=='height' and v['success']]
    result = {'status': 'B17_ACCEPTED_FRONTIER_DIAGNOSTIC_NO_NEW_CREDIT',
              'model_sha256': data['model_sha256'], 'tree_sha256': sha(args.tree),
              'source_manifest_sha256': sha(args.package / 'MANIFEST.json'),
              'native_library_sha256': sha(args.package / 'libb17_native.so') if args.native else None,
              'nodes': len(data['nodes']), 'kinds': dict(kinds), 'E_reasons': dict(e_reasons),
              'open': len(frontiers), 'open_oracle_results': dict(open_reasons),
              'open_depths': dict(sorted(depths.items())), 'zero_straddling_coordinates': dict(signs),
              'complete_prefix_charts': sum(v['complete_prefix_charts'] for v in open_images),
              'unresolved_prefix_charts': sum(not v['complete_prefix_charts'] for v in open_images),
              'canonical_image_widths': widths, 'oracle_audit_seconds': oracle_seconds,
              'profile_samples': len(selected), 'profile_seconds': seconds,
              'sample_certificates': dict(Counter(v['certificate']['kind'] if v['certificate'] else 'NONE' for v in controls)),
              'LP_seconds': sum(v['seconds'] for v in lp_records), 'LP_calls': len(lp_records),
              'height_lp_success': len(height_lps),
              'numeric_height_lps_above_alpha': sum(v['numeric_height_upper'] > float(ALPHA) + 1e-9 for v in height_lps),
              'numeric_only_diagnostics_are_not_bounds_or_counterexamples': True,
              'macro_ledger': '14/15', 'whole_B_closed': False}
    (args.out / 'AUDIT_RESULT.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
