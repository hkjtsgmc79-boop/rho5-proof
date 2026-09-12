#!/usr/bin/env python3
"""Retire only the proved RHO5 runs and record independent complete coverage.

Existing supervisors perform their own checkpoint/owned-process shutdown.
The frozen old-root file and its four original O entries are never changed.
"""
from pathlib import Path
from collections import Counter
import argparse
import fcntl
import hashlib
import json
import os
import time

DEEP = Path('/root/microscope_ws/rho5_deep500_all_open_20260910_08')
LEGACY = Path('/root/microscope_ws/rho5_cqg_continuous_20260910/run_01')
TASK = '435003_bebe09509f4b934c5496'
ROOT_SHA = '8e138dce9a65e49252a1f4714229b1ca95227943913f1eeefdf51714810a563c'
SCHEMA = 'RHO5_PROOF_COMPLETION_ADOPTION_V1'

def need(ok, msg):
    if not ok:
        raise ValueError(msg)

def read(p):
    return json.loads(Path(p).read_text())

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()

def write(p, obj):
    p = Path(p); p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_name(p.name + '.proof_completion.tmp')
    with tmp.open('w') as f:
        json.dump(obj, f, ensure_ascii=False, indent=2); f.write('\n')
        f.flush(); os.fsync(f.fileno())
    os.replace(tmp, p)

def exclusive_stop(p, obj):
    """Never replace a concurrent user/guard STOP; own retries are idempotent."""
    p = Path(p)
    tmp = p.with_name(p.name + '.proof_completion.' + str(os.getpid()) + '.' + str(time.time_ns()))
    try:
        with tmp.open('x') as f:
            json.dump(obj, f, ensure_ascii=False, indent=2); f.write('\n')
            f.flush(); os.fsync(f.fileno())
        try:
            os.link(tmp, p)
        except FileExistsError:
            old = read(p)
            need(old.get('requested_by') == 'proof_completion'
                 and old.get('root_overlay_sha256') == obj['root_overlay_sha256'],
                 'A concurrent user/guard STOP takes precedence: ' + str(p))
    finally:
        tmp.unlink(missing_ok=True)

def proc(pid):
    try:
        root = Path('/proc') / str(pid)
        stat = (root/'stat').read_text().rsplit(')', 1)[1].split()
        args = [x.decode() for x in (root/'cmdline').read_bytes().split(b'\0') if x]
        cwd = (root/'cwd').resolve(strict=True)
        return {'pid':pid, 'ppid':int(stat[1]), 'state':stat[0],
                'start_ticks':stat[19], 'args':args, 'cwd':str(cwd)}
    except (OSError, ValueError, IndexError, UnicodeError):
        return None

def owned_processes():
    found = {}
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():
            continue
        info = proc(int(p.name))
        if not info or info['state'] in ('Z','X') or info['pid'] == os.getpid():
            continue
        found[info['pid']] = info
    seeds = {pid for pid, info in found.items()
             if any(a.startswith(str(DEEP)+'/') or a.startswith(str(LEGACY)+'/') for a in info['args'])
             or any(info['cwd'] == str(root) or info['cwd'].startswith(str(root)+'/')
                    for root in (DEEP, LEGACY))}
    # Catch relative/-c/native solver children as well as their named parents.
    while True:
        children = {pid for pid, info in found.items() if info['ppid'] in seeds}
        if children <= seeds:
            break
        seeds |= children
    return [found[pid] for pid in sorted(seeds)]

def authenticate(args):
    overlay_file = args.overlay.resolve()
    need(str(overlay_file).startswith('/root/microscope_ws/'), 'Wrong workspace')
    need(sha(overlay_file) == args.overlay_sha256, 'Unsealed complete-root receipt')
    overlay = read(overlay_file)
    need(overlay['schema'] == 'RHO5_ACTUAL_ROOT_COMPLETE_SOURCE_OVERLAY_V1'
         and overlay['status'] == 'ACTUAL_ROOT_ALL_OPEN_PARENTS_COVERED'
         and overlay['root_sha256'] == ROOT_SHA and overlay['effective_open_count'] == 0
         and overlay['complete_parents'] == 469
         and overlay['whole_B_closed_by_independent_complete_overlay'] is True,
         'Root is not completely covered')
    need(overlay['actual_root_binding']['status'] == 'ALL_FOUR_ACTUAL_ROOT_OPEN_BOXES_BOUND'
         and {r['index'] for r in overlay['actual_root_binding']['bound_parents']}
         == {338726,435003,563285,675104}, 'Missing exact root residual binding')
    parent_file = Path(overlay['new_parent_receipt']['file'])
    need(sha(parent_file) == overlay['new_parent_receipt']['sha256'], 'Changed final parent receipt')
    parent = read(parent_file)
    need(parent['schema'] == 'RHO5_SOURCE_COMPOSITE_PARENT_V1' and parent['index'] == 435003
         and parent['status'] == 'STRICT_SOURCE_COMPOSITE_PARENT_ACCEPTED'
         and parent['covered_targets'] == 240 and parent['open_targets'] == 0,
         'Last parent incomplete')
    joint_file = (Path(parent['joint_proof_root']) / overlay['joint_anchor_receipt']['file']).resolve()
    need(str(joint_file).startswith('/root/microscope_ws/')
         and sha(joint_file) == overlay['joint_anchor_receipt']['sha256'], 'Complete-anchor reference differs')
    return overlay, {'schema':SCHEMA, 'epoch':time.time(),
        'root_overlay_file':str(overlay_file), 'root_overlay_sha256':args.overlay_sha256,
        'parent_receipt_file':str(parent_file), 'parent_receipt_sha256':sha(parent_file),
        'joint_anchor_receipt_file':str(joint_file),
        'joint_anchor_receipt_sha256':overlay['joint_anchor_receipt']['sha256'],
        'old_root_sha256':ROOT_SHA, 'old_rule_open_count':4,
        'effective_open_count':0, 'complete_parents':469,
        'macro_ledger':'15/15', 'whole_B_alpha_safe':True,
        'proof_scope':'INDEPENDENT_COMPLETE_OVERLAY_ON_PREVIOUSLY_ACCEPTED_FULL_ROOT',
        'producer_file_sha256':sha(__file__), 'model_wakeups':False}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--overlay', type=Path, required=True)
    ap.add_argument('--overlay-sha256', required=True)
    ap.add_argument('--output-dir', type=Path, required=True)
    ap.add_argument('--action', choices=['begin','adopt'], required=True)
    a = ap.parse_args(); out = a.output_dir.resolve()
    need(str(out).startswith('/root/microscope_ws/'), 'Output outside workspace')
    out.mkdir(parents=True, exist_ok=True)
    overlay, record = authenticate(a)
    if a.action == 'begin':
        request_file = out/'RETIREMENT_REQUEST.json'
        retry = request_file.exists()
        if retry:
            prior = read(request_file)
            need(prior['root_overlay_sha256'] == a.overlay_sha256,
                 'Another proof completion already owns this retirement directory')
        deep = read(DEEP/'RUN_STATE.json'); legacy = read(LEGACY/'STATE.json')
        need(legacy['root_sha256'] == ROOT_SHA, 'Production moved to a different root')
        active = [t for t in deep['tasks'].values() if t['status'] in ('RUNNING','STARTING','ALPHA_RETIRING')]
        need(all(t['task_id'] == TASK for t in active), 'Another unretired deep task exists')
        need(all(t['status'] in ('CLOSED','COVERED_BY_PRODUCTION','COVERED_BY_ALPHA')
                 for key,t in deep['tasks'].items() if key != TASK), 'Other original responsibility not settled')
        need(all(v['status'] in ('CLOSED','COVERED_BY_ALPHA')
                 for key,v in legacy['cases'].items() if key != '435003'), 'Another legacy responsibility not settled')
        need(not any(m.get('status') == 'RUNNING' for m in deep['mergers'].values()), 'Merger still active')
        for root in (DEEP,LEGACY):
            if (root/'STOP.json').exists():
                previous = read(root/'STOP.json')
                need(retry and previous.get('requested_by') == 'proof_completion'
                     and previous.get('root_overlay_sha256') == a.overlay_sha256,
                     'An existing stop takes precedence')
        if not retry:
            write(out/'DEEP_STATE_BEFORE.json', deep); write(out/'LEGACY_STATE_BEFORE.json', legacy)
            for name,root in [('DEEP',DEEP),('LEGACY',LEGACY)]:
                write(out/(name+'_STATUS_BEFORE.json'), read(root/'STATUS.json'))
            record['owned_processes_before'] = owned_processes()
            checkpoint = DEEP/deep['tasks'][TASK]['folder']/'final.json'
            need(checkpoint.is_file(), 'Deep checkpoint missing before retirement')
            record['deep_checkpoint_before'] = {'file':str(checkpoint), 'sha256':sha(checkpoint),
                                                'retained_in_place':True}
            record['legacy_inflight_before'] = legacy['cases']['435003'].get('inflight')
            write(request_file, record)
        else:
            record = prior
        stop = {'epoch':time.time(), 'reason':'COMPLETE_PROOF_ACCEPTED_NO_REMAINING_SEARCH',
                'requested_by':'proof_completion', 'root_overlay_file':record['root_overlay_file'],
                'root_overlay_sha256':a.overlay_sha256, 'checkpoints_and_logs_retained':True}
        exclusive_stop(DEEP/'STOP.json', stop)
        exclusive_stop(LEGACY/'STOP.json', dict(stop, mode='immediate'))
        print(json.dumps({'status':'PROVED_RUN_RETIREMENT_REQUESTED','pending_processes':len(record['owned_processes_before'])}))
        return

    request = read(out/'RETIREMENT_REQUEST.json')
    need(request['root_overlay_sha256'] == a.overlay_sha256, 'Wrong retirement session')
    locks = []
    for root in [DEEP,LEGACY]:
        f = (root/'DAEMON.lock').open('a+')
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB); locks.append(f)
    active = owned_processes()
    need(not active, 'Run processes still active: '+str([p['pid'] for p in active]))
    deep = read(DEEP/'RUN_STATE.json'); legacy = read(LEGACY/'STATE.json')
    need(legacy['root_sha256'] == ROOT_SHA and legacy['accepted_open'] == 4, 'Frozen old-root ledger changed')
    need((DEEP/'STOP.json').exists() and (LEGACY/'STOP.json').exists(), 'Permanent run STOP markers disappeared')
    folder = DEEP/deep['tasks'][TASK]['folder']
    checkpoint = folder/'final.json'
    need(checkpoint.is_file(), 'Deep checkpoint was not retained')
    final_sha = sha(checkpoint)
    stopped = read(folder/'STOPPED.json') if (folder/'STOPPED.json').exists() else None
    finished = read(folder/'RESULT.json') if (folder/'RESULT.json').exists() else None
    need(any(r and r.get('task_id') == TASK and r.get('certificate_sha256') == final_sha
             for r in (stopped, finished)), 'No final checkpoint-bound worker exit receipt')
    legacy_checkpoint = LEGACY/legacy['cases']['435003']['certificate']
    need(legacy_checkpoint.is_file()
         and sha(legacy_checkpoint) == legacy['cases']['435003']['certificate_sha256'],
         'Latest accepted legacy checkpoint was not retained')
    write(out/'DEEP_STATE_AFTER_STOP_BEFORE_ADOPTION.json', deep)
    write(out/'LEGACY_STATE_AFTER_STOP_BEFORE_ADOPTION.json', legacy)
    receipt = dict(record, status='COMPLETE_PROOF_ADOPTED_SEARCH_STOPPED',
                   stopped_processes_verified=True, old_root_file_modified=False,
                   deep_checkpoint_after_stop={'file':str(checkpoint),'sha256':final_sha},
                   deep_exit_receipt_file=str(folder/('STOPPED.json' if stopped else 'RESULT.json')),
                   legacy_accepted_checkpoint={'file':str(legacy_checkpoint),'sha256':sha(legacy_checkpoint)})
    task = deep['tasks'][TASK]
    task.update(status='COVERED_BY_SOURCE_COMPOSITE', closed=True,
                complete_anchor_receipt={'file':record['joint_anchor_receipt_file'],
                    'sha256':record['joint_anchor_receipt_sha256']}, finished_epoch=time.time(),
                independent_complete_overlay=receipt)
    deep['parents']['435003'].update(source_composite_strict_accepted=True,
                                     source_composite_receipt=overlay['new_parent_receipt'])
    deep.update(final_overlay=receipt, updated_epoch=time.time())
    case = legacy['cases']['435003']
    if 'inflight' in case:
        case['retired_inflight'] = case.pop('inflight')
        case['retired_inflight_epoch'] = time.time()
    case.update(status='COVERED_BY_SOURCE_COMPOSITE',
                complete_parent_receipt=overlay['new_parent_receipt'], final_overlay=receipt)
    legacy.update(phase='COMPLETE_BY_VERIFIED_OVERLAY', final_overlay=receipt, updated_epoch=time.time())
    legacy['external_coverage_status'] = {'complete_parents':469, 'old_rule_accepted_parents':465,
        'independent_alpha_parents':3, 'independent_source_composite_parents':1,
        'effective_uncovered_parents':0, 'old_rule_accepted_open':4,
        'root_overlay_file':record['root_overlay_file'], 'root_overlay_sha256':a.overlay_sha256}
    write(DEEP/'RUN_STATE.json', deep); write(LEGACY/'STATE.json', legacy)
    ds = read(DEEP/'STATUS.json')
    statuses = Counter(t['status'] for t in deep['tasks'].values())
    ds.update(phase='COMPLETE_BY_VERIFIED_OVERLAY', epoch=time.time(),
              statuses=dict(statuses),
              new_verified_original_branches_closed=sum(statuses[k] for k in
                  ('CLOSED','COVERED_BY_ALPHA','COVERED_BY_SOURCE_COMPOSITE')),
              new_verified_source_composite_original_branches_closed=statuses['COVERED_BY_SOURCE_COMPOSITE'],
              effective_original_branches_closed=sum(statuses[k] for k in
                  ('CLOSED','COVERED_BY_PRODUCTION','COVERED_BY_ALPHA','COVERED_BY_SOURCE_COMPOSITE')),
              strict_source_composite_parents=[435003], effective_uncovered_parents=0,
              active_search_workers=0, active_mergers=0, active_progress=[],
              daemon_alive=False, final_overlay=receipt)
    for row in ds.get('per_parent',[]):
        row['statuses'] = dict(Counter(t['status'] for t in deep['tasks'].values() if t['index']==row['index']))
    ls = read(LEGACY/'STATUS.json')
    ls.update(phase='COMPLETE_BY_VERIFIED_OVERLAY', epoch=time.time(), active_jobs=0,
              active_processes=[], case_states=dict(Counter(c['status'] for c in legacy['cases'].values())),
              effective_uncovered_parents=0, pending_complete_parents=0,
              independent_source_composite_parents=1, complete_parents=469,
              daemon_alive=False, final_overlay=receipt)
    write(DEEP/'STATUS.json', ds); write(LEGACY/'STATUS.json', ls)
    for root in [DEEP,LEGACY]:
        write(root/'FINAL_COMPLETE_OVERLAY_ADOPTION.json', receipt)
    write(out/'PRODUCTION_COMPLETION.json', dict(receipt,
        deep_state_sha256=sha(DEEP/'RUN_STATE.json'), legacy_state_sha256=sha(LEGACY/'STATE.json'),
        deep_checkpoint_file=record.get('deep_checkpoint_before',request['deep_checkpoint_before'])['file'],
        checkpoints_and_logs_retained=True, still_running_owned_processes=[]))
    print(json.dumps({'status':receipt['status'],'complete_parents':469,'effective_open_count':0,'macro_ledger':'15/15'}))

if __name__ == '__main__':
    main()
