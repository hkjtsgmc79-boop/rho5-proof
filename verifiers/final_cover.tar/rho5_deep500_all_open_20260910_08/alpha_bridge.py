"""Single-writer scheduler bridge for independently accepted alpha covers.

This module never discovers a bound or creates a mathematical acceptance.
It consumes immutable cut/receipt pairs through alpha_parent_cover, then asks
only the corresponding owned search to save and exit. Existing work is kept.
"""
from pathlib import Path
import hashlib
import json
import os
import time
import traceback

import alpha_cover as ac
import alpha_parent_cover as apc
from fast_checkpoint import atomic_json

PAID = {'CLOSED', 'COVERED_BY_PRODUCTION', 'COVERED_BY_ALPHA'}


def read(path):
    return json.loads(Path(path).read_text())


class AlphaBridge:
    def __init__(self, root, coordinator, alive_function):
        self.root = Path(root).resolve()
        self.c = coordinator
        self._alive = alive_function
        self.registry_path = self.root/'alpha_v1/REGISTRY.json'
        self.enabled = self.registry_path.parent.exists()
        self.registry_stamp = None
        self.handled = set()
        self.anchors = {}
        self.task_versions = {}
        self.parent_last = {}
        self.parent_dirty = set()
        self.errors = set()
        self.verified_retirements = set()
        self.file_hashes = {}
        if self.enabled:
            ac.configure(self.root/'alpha_v1/b14_runtime')
        for key, p in self.c.state['parents'].items():
            if p.get('alpha_mode'):
                self.parent_dirty.add(key)
        self.recover_composition()

    def owned(self, name):
        path = (self.root/name).resolve()
        if not path.is_relative_to(self.root):
            raise ValueError('Alpha input escapes this run')
        return path

    @staticmethod
    def digest(value):
        return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()).hexdigest()

    def file_sha(self, path):
        path = self.owned(path)
        s = path.stat()
        stamp = (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        old = self.file_hashes.get(path)
        if old is None or old[0] != stamp:
            h = hashlib.sha256()
            with path.open('rb') as f:
                for block in iter(lambda: f.read(1024*1024), b''):
                    h.update(block)
            after = path.stat()
            if stamp != (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns):
                raise ValueError('Alpha input changed while hashing')
            self.file_hashes[path] = (stamp, h.hexdigest())
        return self.file_hashes[path][1]

    def anchor(self, key):
        import parents_merger as pm
        if key not in self.anchors:
            anchor_path = self.owned(self.c.state['parents'][key]['anchor_file'])
            if anchor_path != self.root/'anchors'/key/'ANCHOR.json':
                raise ValueError('Noncanonical original anchor record')
            ar = read(anchor_path)
            parent_path = self.owned(ar['parent_file'])
            base_path = self.owned(ar['anchor_base_file'])
            parent = read(parent_path)
            if ar['index'] != int(key) or parent['index'] != int(key):
                raise ValueError('Original anchor parent identity differs')
            migration_path = self.owned(ar['migration_file'])
            base, paid = pm.migration(base_path, self.c.inputs.bp, parent, migration_path)
            targets = sorted(pm.old_open_paths(base['tree']))
            declared = ar.get('original_open_paths')
            if (not isinstance(declared, list) or not targets or any(not isinstance(p,str) or any(c not in '01' for c in p) for p in declared)
                    or len(set(declared)) != len(declared) or sorted(declared) != targets
                    or any(q.startswith(p) for p,q in zip(targets, targets[1:]))
                    or ar.get('source_certificate_sha256') != paid['legacy_certificate_file_sha256']):
                raise ValueError('Original OPEN partition or paid source identity differs')
            selected = [t for t in self.c.state['tasks'].values() if str(t['index']) == key]
            if (sorted(t['target_path'] for t in selected) != targets
                    or any(t['task_id'] != key+'_'+hashlib.sha256(t['target_path'].encode()).hexdigest()[:20] for t in selected)):
                raise ValueError('Original OPEN tasks are missing, duplicated, or misowned')
            m = read(migration_path)
            paths = [anchor_path, migration_path]
            paths += [self.owned(migration_path.parent/m[k]) for k in
                      ('legacy_certificate_file','source_result_file','base_file','parent_file')]
            self.anchors[key] = (ar, parent_path, base, {p:self.file_sha(p) for p in paths})
        for path, sha in self.anchors[key][3].items():
            if self.file_sha(path) != sha:
                raise ValueError('Authenticated original anchor changed')
        return self.anchors[key][:3]

    def note_error(self, identity, exc):
        if identity in self.errors:
            return
        self.errors.add(identity)
        self.c.event('ALPHA_ADOPTION_REJECTED', identity=identity, error=str(exc))
        p = self.root/'alpha_v1/ADOPTION_ERRORS.jsonl'
        with p.open('a') as f:
            f.write(json.dumps({'epoch':time.time(),'identity':identity,
                                'error':str(exc)})+'\n')

    def adopt(self, task, ref, evidence):
        key = str(task['index'])
        # These are our own searches; normal checkpoint stop preserves the state.
        if self.c_alive(task):
            folder = self.owned(task['folder'])
            stop = folder/'STOP.json'
            if not stop.exists():
                temp = folder/('ALPHA_STOP.tmp.'+str(os.getpid())+'.'+str(time.time_ns()))
                atomic_json(temp, {'epoch':time.time(),'reason':'ALPHA_SOURCE_PROVED',
                                  'acceptance_file':ref['acceptance_file'],
                                  'acceptance_sha256':ref['acceptance_sha256'],
                                  'preserve_latest_checkpoint':True})
                try:
                    os.link(temp, stop)  # Never overwrite a concurrent user/guard STOP.
                except FileExistsError:
                    pass
                finally:
                    temp.unlink(missing_ok=True)
            task['status'] = 'ALPHA_RETIRING'
        else:
            task.update(status='COVERED_BY_ALPHA',closed=True,finished_epoch=time.time())
        task['alpha_coverage'] = ref
        task['alpha_binding'] = evidence
        task.setdefault('alpha_accepted_epoch', time.time())
        self.verified_retirements.add(task['task_id'])
        p = self.c.state['parents'][key]
        p['alpha_mode'] = True
        p['dirty'] = False
        self.parent_dirty.add(key)
        self.c.event('ALPHA_SOURCE_ADOPTED', task_id=task['task_id'],
                     index=task['index'], cut_file=ref['cut_certificate_file'],
                     state=task['status'])

    def check_existing_task(self, task, parent_path, anchor):
        """A live task must still be an exact extension of this owned old OPEN."""
        import parents_merger as pm
        import deep_math as dm
        path = self.owned(task['folder'])/'TASK.json'
        if not path.exists():
            if self.c_alive(task):
                raise ValueError('Live task lacks immutable TASK.json')
            return
        request = read(path)
        for key in ('task_id','index','target_path'):
            if request[key] != task[key]:
                raise ValueError('Current task ownership mismatch: '+key)
        anchor_path = self.owned(self.c.state['parents'][str(task['index'])]['anchor_file'])
        if (self.owned(request['original_open_anchor_file']) != anchor_path
                or self.file_sha(anchor_path) != request['original_open_anchor_sha256']):
            raise ValueError('Current task original anchor record differs')
        if (self.file_sha(parent_path) != request['parent_sha256']
                or self.file_sha(self.owned(request['parent_file'])) != request['parent_sha256']):
            raise ValueError('Current task has another physical parent')
        if self.file_sha(self.owned(request['base_file'])) != request['input_sha256']:
            raise ValueError('Current task input bytes changed')
        migration_path = self.owned(request['migration_file'])
        key = (self.file_sha(anchor_path), request['base_file'],request['input_sha256'], self.file_sha(migration_path))
        if key not in self.task_versions:
            base, _ = pm.migration(pm.owned(request['base_file']),self.c.inputs.bp,
                                   read(parent_path),migration_path)
            pm.extension(anchor,base)
            m = read(migration_path)
            paths = [migration_path] + [self.owned(migration_path.parent/m[k]) for k in
                      ('legacy_certificate_file','source_result_file','base_file','parent_file')]
            self.task_versions[key] = {p:self.file_sha(p) for p in paths}
        for path, sha in self.task_versions[key].items():
            if self.file_sha(path) != sha:
                raise ValueError('Authenticated current-task source changed')

    def c_alive(self, task):
        # Use the coordinator's established pid + start-tick + entrypoint check.
        return self._alive(task)

    def stopping(self):
        return self.c.stop_signal or (self.root/'STOP.json').exists()

    def update(self):
        if not self.enabled:
            return
        changed = False
        # recover() may have restored an owned live PID to RUNNING. Revalidate
        # persisted evidence before either requesting its exit or granting credit.
        for task in self.c.state['tasks'].values():
            if not task.get('alpha_coverage') or task['status'] in ('CLOSED','COVERED_BY_PRODUCTION'):
                continue
            try:
                if task['task_id'] not in self.verified_retirements:
                    _, parent_path, anchor = self.anchor(str(task['index']))
                    evidence = apc.verify_alpha_evidence(self.root,self.c.inputs.bp,parent_path,
                                  task['alpha_coverage'],anchor,task['target_path'])
                    self.check_existing_task(task,parent_path,anchor)
                    self.adopt(task,task['alpha_coverage'],evidence)
                    changed = True
                elif task['status'] == 'ALPHA_RETIRING' and not self.c_alive(task):
                    task.update(status='COVERED_BY_ALPHA',closed=True,finished_epoch=time.time())
                    self.parent_dirty.add(str(task['index']))
                    self.c.event('ALPHA_SEARCH_RETIRED_CHECKPOINT_PRESERVED',
                                 task_id=task['task_id'],index=task['index'])
                    changed = True
            except Exception as exc:
                if task['status'] == 'COVERED_BY_ALPHA':
                    task.update(status='ALPHA_EVIDENCE_REJECTED',closed=False)
                    p = self.c.state['parents'][str(task['index'])]
                    p.update(strict_accepted=False,alpha_strict_accepted=False)
                    changed = True
                self.note_error('retirement:'+task['task_id'],exc)
        if not self.stopping() and self.registry_path.exists():
            try:
                st = self.registry_path.stat()
                stamp = (st.st_mtime_ns, st.st_size)
                if stamp != self.registry_stamp:
                    registry = read(self.registry_path)
                    if registry.get('schema') != 'RHO5_ALPHA_REGISTRY_V1' or not isinstance(registry.get('accepted'),dict):
                        raise ValueError('Wrong alpha registry schema')
                    for cid, entry in registry['accepted'].items():
                        if cid in self.handled:
                            continue
                        try:
                            if cid != entry['cut_certificate_sha256']:
                                raise ValueError('Registry key/certificate mismatch')
                            key = str(entry['index'])
                            if key not in self.c.state['parents']:
                                continue
                            _, parent_path, anchor = self.anchor(key)
                            ref = {k:entry[k] for k in ('cut_certificate_file',
                                   'cut_certificate_sha256','acceptance_file','acceptance_sha256')}
                            for task in self.c.state['tasks'].values():
                                if (str(task['index']) != key or task['status'] in PAID
                                        or task['status'] == 'ALPHA_RETIRING'
                                        or not task['target_path'].startswith(entry['cut_path'])):
                                    continue
                                try:
                                    evidence = apc.verify_alpha_evidence(
                                        self.root,self.c.inputs.bp,parent_path,ref,
                                        anchor,task['target_path'])
                                    self.check_existing_task(task,parent_path,anchor)
                                    self.adopt(task,ref,evidence)
                                    changed = True
                                except Exception as exc:
                                    self.note_error(cid+':'+task['task_id'],exc)
                            self.handled.add(cid)
                        except Exception as exc:
                            self.note_error('registry:'+cid,exc)
                    self.registry_stamp = stamp
            except Exception as exc:
                self.note_error('registry',exc)
        for key, p in self.c.state['parents'].items():
            if p.get('alpha_mode') and p.get('dirty'):
                self.parent_dirty.add(key)
                p['dirty'] = False
                changed = True
        if changed:
            self.c.save()
        self.compose()

    def parent_tasks(self, key):
        return {tid:t for tid,t in self.c.state['tasks'].items() if str(t['index']) == key}

    def recover_composition(self):
        # One process across restarts, including a spawn just before save().
        entry = str(self.root/'alpha_parent_cover.py')
        matches = []
        for proc in Path('/proc').glob('[0-9]*'):
            try:
                args = [x.decode() for x in (proc/'cmdline').read_bytes().split(b'\0') if x]
                if entry not in args:
                    continue
                tail = (proc/'stat').read_text().rsplit(')',1)[1].split()
                key = args[args.index(entry)+1]
                if key not in self.c.state['parents'] or tail[0] in ('Z','X'):
                    continue
                matches.append({'pid':int(proc.name),'start_ticks':tail[19],
                                'entrypoint':entry,'index':key,'status':'RUNNING'})
            except (OSError, ValueError, IndexError, UnicodeError):
                continue
        job = self.c.state.get('alpha_composition')
        if matches:
            if len(matches) != 1:
                # Keep all process identities visible to STOP/resource accounting.
                self.c.state['alpha_composition_extra_processes'] = matches
                self.note_error('composition-recovery',ValueError('Multiple alpha composition processes; no new dispatch'))
                return
            found = matches[0]
            if job and str(job.get('index')) == found['index'] and job.get('status') in ('STARTING','RUNNING'):
                job.update(found)
            else:
                # Unknown launch provenance cannot credit an existing receipt.
                self.c.state['alpha_composition'] = {**found,'untrusted_recovery':True}
            self.c.save()

    def harvest_composition(self):
        job = self.c.state.get('alpha_composition')
        if not job or job.get('status') not in ('STARTING','RUNNING') or self.c_alive(job):
            return
        key = str(job['index'])
        try:
            if job.get('untrusted_recovery'):
                raise ValueError('Recovered composition lacks a durable launch provenance')
            path = self.root/'parents'/key/'ALPHA_COMPOSITE_RESULT.json'
            result = read(path)
            sha = self.file_sha(path)
            current = self.parent_tasks(key)
            observed = result.get('observed_parent_task_state')
            if (result.get('schema') != apc.SCHEMA or result.get('index') != int(key)
                    or result.get('epoch',0) < job['started_epoch']
                    or path.stat().st_mtime < job['started_epoch']
                    or sha == job.get('previous_receipt_sha256')
                    or result.get('composition_implementation_sha256') != job['implementation_sha256']
                    or self.file_sha(self.root/'alpha_parent_cover.py') != job['implementation_sha256']
                    or result.get('deep_rule_identity') != self.c.inputs.bp.rule_hash()
                    or result.get('alpha_rule_identity') != ac.rule_identity()
                    or result.get('observed_parent_task_state_sha256') != self.digest(observed)
                    or self.digest(observed) != job['task_state_sha256']):
                raise ValueError('Composition receipt is stale or belongs to another launch/source')
            if self.digest(current) != job['task_state_sha256']:
                job['status'] = 'SUPERSEDED'
                self.parent_dirty.add(key)
                self.c.event('ALPHA_COMPOSITION_SOURCE_ADVANCED',index=int(key))
                self.c.save()
                return
            manifest = result['evidence_manifest']
            if not isinstance(manifest,list) or self.digest(manifest) != result['evidence_manifest_sha256']:
                raise ValueError('Composition evidence manifest differs')
            for row in manifest:
                if self.file_sha(self.owned(row['file'])) != row['sha256']:
                    raise ValueError('Composition input changed: '+row['file'])
            ar, parent_path, _ = self.anchor(key)
            targets = sorted(ar['original_open_paths'])
            rows = result['targets']
            expected_source = self.digest({'index':int(key),'anchor_sha256':result.get('anchor_sha256'),
                                           'original_open_paths':targets,'targets':rows})
            if (result.get('parent_sha256') != self.file_sha(parent_path)
                    or result.get('source_signature') != expected_source
                    or result.get('anchor_sha256') != self.file_sha(self.owned(ar['anchor_base_file']))
                    or result.get('original_open_paths') != targets
                    or result.get('total_original_targets') != len(targets)
                    or len(rows) != len(targets)
                    or sorted(r['target_path'] for r in rows) != targets
                    or result.get('covered_targets',0)+result.get('open_targets',0) != len(targets)
                    or result.get('status') not in (apc.ACCEPTED,'OPEN')
                    or (result['status'] == apc.ACCEPTED) != (result['open_targets'] == 0)
                    or result.get('old_frozen_rule_acceptance') is not False
                    or result.get('whole_root_credit') is not False):
                raise ValueError('Composition receipt scope/counts differ')
            closed = result['status'] == apc.ACCEPTED
            p = self.c.state['parents'][key]
            p.update(alpha_strict_accepted=closed,strict_accepted=closed,
                     alpha_composite_file=str(path.relative_to(self.root)),
                     alpha_composite_sha256=sha,alpha_composite_source_signature=result['source_signature'],
                     alpha_composite_task_state_sha256=job['task_state_sha256'],
                     dirty=False,merge_error=False)
            job.update(status='COMPLETE',receipt_sha256=sha,finished_epoch=time.time())
            self.parent_dirty.discard(key)
            self.c.event('ALPHA_PARENT_COVER_UPDATED',index=int(key),status=result['status'],
                         covered_targets=result['covered_targets'],open_targets=result['open_targets'])
        except Exception as exc:
            job.update(status='ERROR',finished_epoch=time.time(),error=str(exc))
            self.parent_dirty.add(key)
            self.note_error('composition:'+key+':'+str(job.get('started_epoch')),exc)
            atomic_json(self.root/'alpha_v1'/('PARENT_'+key+'_ERROR.json'),
                        {'epoch':time.time(),'error':traceback.format_exc(),
                         'old_inputs_preserved':True,'credit_granted':False})
        self.c.save()

    def compose(self):
        self.harvest_composition()
        if self.stopping():
            return
        extras = self.c.state.get('alpha_composition_extra_processes',[])
        if any(self.c_alive(row) for row in extras):
            return
        job = self.c.state.get('alpha_composition')
        if job and job.get('status') in ('STARTING','RUNNING'):
            return
        now = time.time()
        for key in sorted(self.parent_dirty):
            tasks = self.parent_tasks(key)
            signature = self.digest(tasks)
            p = self.c.state['parents'][key]
            # Retry only on a real source-state change; errors retain their files.
            if p.get('alpha_composition_attempted_state_sha256') == signature:
                continue
            if any(t['status'] == 'ALPHA_RETIRING' for t in tasks.values()):
                continue
            merger = self.c.state['mergers'].get(key)
            if merger and merger.get('status') == 'RUNNING' and self.c_alive(merger):
                continue
            try:
                path = self.root/'parents'/key/'ALPHA_COMPOSITE_RESULT.json'
                job = {'index':key,'status':'STARTING','started_epoch':now,
                       'task_state_sha256':signature,
                       'implementation_sha256':self.file_sha(self.root/'alpha_parent_cover.py'),
                       'previous_receipt_sha256':self.file_sha(path) if path.exists() else None}
                self.c.state['alpha_composition'] = job
                p['alpha_composition_attempted_state_sha256'] = signature
                self.c.save()
                process = self.c.start_child('alpha_parent_cover.py',[key,'--root',str(self.root)],
                                self.root/'parents'/key/'ALPHA_COMPOSITE.log')
                job.update(process)
                job['started_epoch'] = now
                self.c.save()
                # The scheduler already runs nice 10; also set it explicitly.
                os.setpriority(os.PRIO_PROCESS,process['pid'],10)
                # Preserve the earlier boundary preceding all child reads.
                self.c.event('ALPHA_PARENT_COMPOSITION_STARTED',index=int(key),pid=job['pid'])
            except Exception as exc:
                # A child may already exist: retain RUNNING identity if recorded.
                if job and not self.c_alive(job):
                    job.update(status='ERROR',error=str(exc))
                self.note_error('composition-launch:'+key,exc)
                self.c.save()
            return
