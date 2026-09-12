"""Compose paid original-OPEN coverage without inventing an old-rule tree.

Old C/H/A mathematics and closed worker mathematics are reused through the
existing parents_merger receipt checks. New alpha mathematics must already have
an independent alpha_cover.verify_cut receipt. This module checks its bytes and
domain binding, then accounts for every original OPEN exactly once. It never
calls a mathematical verifier or modifies old COVERAGE/MERGED/MERGE_DONE files.
"""
from pathlib import Path
from contextvars import ContextVar
import argparse
import hashlib
import importlib
import json
import os
import sys
import time
import traceback
import types

ROOT = Path(__file__).resolve().parent
SCHEMA = "RHO5_ALPHA_COMPOSITE_PARENT_V1"
ACCEPTED = "STRICT_ALPHA_COMPOSITE_PARENT_ACCEPTED"
CUT_RECEIPT_SCHEMA = "RHO5_SOURCE_BOUND_ALPHA_CUT_ACCEPTANCE_V1"
REF_FIELDS = ("cut_certificate_file", "cut_certificate_sha256",
              "acceptance_file", "acceptance_sha256")
_ACTIVE = ContextVar("rho5_alpha_composition_inputs", default=None)


class _InputSnapshot:
    """One composition's immutable files, not a persistent acceptance cache.

    Stat identities detect atomic replacement and in-place changes. Shared
    bases/receipts are decoded once. Individual worker projections are released
    after their target, so hundreds of unique finals cannot accumulate in RAM.
    """
    def __init__(self, root, transient_folders=()):
        self.root = root
        self.transient_folders = tuple(_owned(root, p) for p in transient_folders)
        self.entries, self.shared_objects, self.alpha_records = {}, set(), {}
        self.stats = {"file_reads": 0, "json_parses": 0, "file_cache_hits": 0,
                      "migration_checks": 0, "migration_cache_hits": 0,
                      "extension_checks": 0, "extension_cache_hits": 0,
                      "alpha_receipt_checks": 0, "alpha_receipt_cache_hits": 0}

    @staticmethod
    def fingerprint(path):
        s = path.stat()
        return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)

    def entry(self, path):
        path = _owned(self.root, path)
        stamp = self.fingerprint(path)
        old = self.entries.get(path)
        if old is not None:
            if old["stamp"] != stamp:
                raise ValueError("Evidence changed during parent composition: " + str(path))
            self.stats["file_cache_hits"] += 1
            return old
        item = {"stamp": stamp, "transient": any(path.is_relative_to(p) for p in self.transient_folders)}
        self.entries[path] = item
        return item

    def raw(self, path):
        path = _owned(self.root, path)
        item = self.entry(path)
        if "raw" not in item:
            raw = path.read_bytes()
            if self.fingerprint(path) != item["stamp"]:
                raise ValueError("Evidence changed while being read: " + str(path))
            sha = hashlib.sha256(raw).hexdigest()
            if "sha256" in item and item["sha256"] != sha:
                raise ValueError("Evidence bytes differ from the composition snapshot")
            item.update(raw=raw, sha256=sha)
            self.stats["file_reads"] += 1
        return item["raw"]

    def json(self, path):
        item = self.entry(path)
        raw = self.raw(path)
        if "json" not in item:
            value = json.loads(raw)
            if not isinstance(value, dict):
                raise ValueError("Evidence must be a JSON object")
            item["json"] = value
            self.stats["json_parses"] += 1
            if not item["transient"]:
                self.shared_objects.add(id(value))
                if isinstance(value.get("tree"), dict):
                    self.shared_objects.add(id(value["tree"]))
        return raw, item["json"]

    def sha(self, path):
        item = self.entry(path)
        if "sha256" not in item:
            self.raw(path)
        return item["sha256"]

    def finish_target(self):
        for item in self.entries.values():
            if item["transient"]:
                item.pop("raw", None)
                item.pop("json", None)

    def ensure_unchanged(self):
        for path, item in self.entries.items():
            if self.fingerprint(path) != item["stamp"]:
                raise ValueError("Evidence changed before parent receipt completion: " + str(path))


class _PaidChecks:
    """Private bindings of the existing paid checkers; no live globals patched."""
    def __init__(self, pm, snapshot):
        self.original, self.snapshot = pm, snapshot
        self.migrations, self.extensions, self.digests, self.counted = {}, {}, {}, {}
        namespace = dict(getattr(pm.migration, "__globals__", {}))

        def clone(fn):
            if not isinstance(fn, types.FunctionType):
                return fn
            # Test doubles are not members of the real parents_merger module.
            if fn.__globals__.get("__name__") != getattr(pm, "__name__", None):
                return fn
            result = types.FunctionType(fn.__code__, namespace, fn.__name__, fn.__defaults__, fn.__closure__)
            result.__kwdefaults__ = fn.__kwdefaults__
            return result

        self._migration = clone(pm.migration)
        self._extension = clone(pm.extension)
        self.check_worker_result = clone(pm.check_worker_result)
        namespace.update(read=lambda p: snapshot.json(p)[1], file_sha=snapshot.sha,
                         migration=self.migration, extension=self.extension,
                         digest=self.digest, counts=self.counts)

    def __getattr__(self, name):
        return getattr(self.original, name)

    def migration(self, base_path, bp, parent, migration_path=None):
        base = _owned(self.snapshot.root, base_path)
        mp = _owned(self.snapshot.root, migration_path) if migration_path else base.parent / "MIGRATION.json"
        # Every cache access still verifies that the immutable file identities
        # have not changed. All manifest members are checked again at completion.
        key = (str(base), self.snapshot.sha(base), str(mp), self.snapshot.sha(mp), id(bp), self.digest(parent))
        if key not in self.migrations:
            self.snapshot.stats["migration_checks"] += 1
            self.migrations[key] = self._migration(base, bp, parent, mp)
        else:
            self.snapshot.stats["migration_cache_hits"] += 1
        return self.migrations[key]

    def extension(self, before, after):
        key = (id(before), id(after))
        if key not in self.extensions:
            self.snapshot.stats["extension_checks"] += 1
            self.extensions[key] = (before, after, self._extension(before, after))
        else:
            self.snapshot.stats["extension_cache_hits"] += 1
        return self.extensions[key][2]

    def digest(self, value):
        if id(value) not in self.snapshot.shared_objects:
            return self.original.digest(value)
        if id(value) not in self.digests:
            self.digests[id(value)] = self.original.digest(value)
        return self.digests[id(value)]

    def counts(self, value):
        if id(value) not in self.snapshot.shared_objects:
            return self.original.counts(value)
        if id(value) not in self.counted:
            self.counted[id(value)] = self.original.counts(value)
        return self.counted[id(value)]


def _digest(value):
    raw = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
    return hashlib.sha256(raw).hexdigest()


def _sha(path):
    active = _ACTIVE.get()
    if active is not None:
        return active.sha(path)
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _owned(root, name):
    if not isinstance(name, (str, Path)):
        raise TypeError("Evidence path must be a string or Path")
    path = (root / name).resolve()
    if not path.is_relative_to(root):
        raise ValueError("Evidence is outside the isolated task root")
    return path


def _json(path):
    active = _ACTIVE.get()
    if active is not None:
        return active.json(path)
    raw = Path(path).read_bytes()
    value = json.loads(raw)
    if not isinstance(value, dict):
        raise ValueError("Evidence must be a JSON object")
    return raw, value


def _hash_string(value):
    return isinstance(value, str) and len(value) == 64 and all(c in "0123456789abcdef" for c in value)


def _peer(root, name):
    """Use the same live deep-root modules as the coordinator; reject pollution."""
    expected = root / (name + ".py")
    found = sys.modules.get(name)
    if found is not None and Path(found.__file__).resolve() != expected:
        raise ImportError("Mixed root import: " + name)
    if str(root) not in sys.path:
        sys.path.insert(0, str(root))
    module = importlib.import_module(name)
    if Path(module.__file__).resolve() != expected:
        raise ImportError("Wrong module origin: " + name)
    if name == "parents_merger" and Path(module.ROOT).resolve() != root:
        raise ImportError("parents_merger.ROOT differs from the live deep root")
    return module


def verify_alpha_evidence(root, bp, parent_path, alpha_ref, base_certificate, target_path):
    """Reuse an independent cut receipt and bind its full domain to target.

    This is a byte/identity/structure check, NOT fresh mathematical validation.
    The caller must authenticate base_certificate's paid migration/extension.
    The accepted cut must be at or above the WHOLE original O target, with
    identical pre-cut source ancestors. For a current S extension, compose this
    anchor binding with parents_merger.extension rather than claiming S is O.
    The alpha module must have been configured with its pinned B14 directory.
    """
    root = Path(root).resolve()
    ac, parent_raw, parent, cut_raw, cut, receipt, cut_path, receipt_path, cut_sha, receipt_sha = _paid_alpha_record(
        root, bp, parent_path, alpha_ref)
    if isinstance(base_certificate, (str, Path)):
        base_certificate = _owned(root, base_certificate)
        # Give the structural binder the already decoded immutable base. Its
        # canonical envelope and every target ancestor are still checked; avoid
        # reparsing a potentially large identical base for every original OPEN.
        if _ACTIVE.get() is not None:
            base_sha = _sha(base_certificate)
            base_certificate = _json(base_certificate)[1]
        else:
            base_sha = None
    else:
        base_sha = None
    binding = ac.coverage_binding(bp, (parent_raw, parent), base_certificate,
                                  (cut_raw, cut), target_path)
    if (binding is None or binding.get("status") != "EXACT_ORIGINAL_OPEN_COVER_BINDING"
            or binding.get("requires_independent_cut_acceptance") is not True
            or binding.get("mathematical_acceptance") is not False
            or binding.get("cut_certificate_sha256") != cut_sha
            or binding.get("cut_certificate_object_sha256") != ac.digest(cut)
            or binding.get("parent_raw_sha256") != hashlib.sha256(parent_raw).hexdigest()
            or binding.get("target_path") != target_path):
        raise ValueError("Accepted alpha cut does not cover the complete target source")
    if base_sha is not None:
        binding = {**binding, "base_certificate_sha256": base_sha,
                   "base_original_bytes_bound_by_composition_snapshot": True}
    return {"status": "PAID_ALPHA_CUT_REUSED_AND_SOURCE_BOUND", "target_path": target_path,
            "semantic": receipt["status"], "terminal_kind": cut["terminal"]["kind"],
            "rule": ac.RULE, "rule_identity": receipt["rule_identity"],
            "cut_certificate_file": str(cut_path.relative_to(root)), "cut_certificate_sha256": cut_sha,
            "acceptance_file": str(receipt_path.relative_to(root)), "acceptance_sha256": receipt_sha,
            "parent_raw_sha256": receipt["parent_raw_sha256"], "cut_path": cut["cut_path"],
            "source_image_sha256": receipt.get("source_image_sha256"), "coverage_binding": binding,
            "independent_mathematical_receipt_reused": True,
            "new_mathematical_replay_performed": False, "whole_root_credit": False}


def _paid_alpha_record(root, bp, parent_path, alpha_ref):
    """Check each immutable cut/receipt once per composition, never per target."""
    ac = _peer(root, "alpha_cover")
    parent_path = _owned(root, parent_path)
    parent_raw, parent = _json(parent_path)
    if not isinstance(alpha_ref, dict) or any(k not in alpha_ref for k in REF_FIELDS):
        raise ValueError("Incomplete independent alpha evidence reference")
    for key in ("cut_certificate_sha256", "acceptance_sha256"):
        if not _hash_string(alpha_ref[key]):
            raise ValueError("Invalid alpha evidence SHA256: " + key)
    cut_path = _owned(root, alpha_ref["cut_certificate_file"])
    receipt_path = _owned(root, alpha_ref["acceptance_file"])
    cut_raw, cut = _json(cut_path)
    receipt_raw, receipt = _json(receipt_path)
    cut_sha, receipt_sha = hashlib.sha256(cut_raw).hexdigest(), hashlib.sha256(receipt_raw).hexdigest()
    if cut_sha != alpha_ref["cut_certificate_sha256"] or receipt_sha != alpha_ref["acceptance_sha256"]:
        raise ValueError("Independent alpha evidence bytes changed")
    parent_sha = hashlib.sha256(parent_raw).hexdigest()
    active = _ACTIVE.get()
    cache_key = (id(bp), id(ac), parent_sha, str(cut_path), cut_sha, str(receipt_path), receipt_sha)
    if active is not None and cache_key in active.alpha_records:
        active.stats["alpha_receipt_cache_hits"] += 1
        return active.alpha_records[cache_key]
    if active is not None:
        active.stats["alpha_receipt_checks"] += 1
    identity = ac.rule_identity()
    expect = bp.binding(parent)
    terminal = cut.get("terminal", {})
    kind = terminal.get("kind")
    if (cut.get("schema") != ac.CUT_SCHEMA or cut.get("rule") != ac.RULE
            or cut.get("rule_identity") != identity
            or receipt.get("schema") != CUT_RECEIPT_SCHEMA or receipt.get("rule") != ac.RULE
            or receipt.get("rule_identity") != identity
            or receipt.get("certificate_sha256") != cut_sha
            or receipt.get("certificate_object_sha256") != ac.digest(cut)
            or receipt.get("parent_raw_sha256") != parent_sha
            or receipt.get("parent_binding") != expect
            or receipt.get("parent_index") != parent["index"]
            or receipt.get("profile") != cut.get("source", {}).get("profile")
            or receipt.get("cut_path") != cut.get("cut_path")
            or receipt.get("terminal_kind") != kind
            or receipt.get("mathematical_acceptance") is not True
            or receipt.get("mathematical_replay_performed") is not True
            or receipt.get("independent_verifier") is not True
            or receipt.get("cross_check") is not True
            or receipt.get("old_frozen_rule_acceptance") is not False
            or receipt.get("whole_parent_closed") is not False
            or receipt.get("lineage_nodes") != len(cut.get("lineage", []))):
        raise ValueError("Independent alpha acceptance identity or scope differs")
    status = receipt.get("status")
    if kind == "ALPHA_SAFE":
        port = receipt.get("port_acceptance", {})
        if (status != "ALPHA_SAFE" or not _hash_string(receipt.get("source_image_sha256"))
                or not isinstance(port, dict) or port.get("rule") != ac.PORT_RULE
                or port.get("status") != "ALPHA_SAFE"
                or port.get("method") != terminal.get("port", {}).get("method")
                or port.get("source_image_sha256") != receipt["source_image_sha256"]
                or receipt.get("does_not_prove_gamma_infeasibility") is not True):
            raise ValueError("Alpha port receipt does not match its source cut")
    elif kind == "EMPTY_INTERVAL":
        if status != "EMPTY_INTERVAL" or receipt.get("source_image_sha256") is not None or receipt.get("port_acceptance") is not None:
            raise ValueError("Interval-empty receipt does not match its terminal")
    elif kind == "EXACT_SUBTREE":
        if status not in ("ALPHA_SAFE", "EMPTY_INTERVAL") or not isinstance(receipt.get("subtree_counts"), dict):
            raise ValueError("Missing independently accepted complete subtree")
        if receipt["subtree_counts"].get("O", 0) != 0:
            raise ValueError("Independent alpha subtree still contains OPEN")
    else:
        raise ValueError("Unsupported independent alpha terminal")
    answer = (ac, parent_raw, parent, cut_raw, cut, receipt, cut_path, receipt_path, cut_sha, receipt_sha)
    if active is not None:
        active.alpha_records[cache_key] = answer
    return answer


class _Manifest:
    def __init__(self, root):
        self.root, self.files = root, {}

    def add(self, path, role, expected=None):
        path = _owned(self.root, path)
        sha = _sha(path)
        if expected is not None and sha != expected:
            raise ValueError("Evidence changed while composing: " + str(path))
        rel = str(path.relative_to(self.root))
        previous = self.files.get(rel)
        if previous is not None and previous["sha256"] != sha:
            raise ValueError("Evidence changed during parent composition: " + rel)
        row = self.files.setdefault(rel, {"file": rel, "sha256": sha, "roles": []})
        if role not in row["roles"]:
            row["roles"].append(role)
        return sha

    def migration(self, ref, role):
        mp = _owned(self.root, ref["migration_file"])
        self.add(mp, role + ":migration", ref["migration_file_sha256"])
        _, m = _json(mp)
        for key in ("legacy_certificate_file", "source_result_file", "base_file", "parent_file"):
            if Path(m[key]).name != m[key]:
                raise ValueError("Migration member is not version-local")
            self.add(mp.parent / m[key], role + ":" + key, m[key + "_sha256"])

    def rows(self):
        return [self.files[key] for key in sorted(self.files)]


def _task_input(root, pm, bp, parent, anchor, task_id, task_state, manifest):
    folder = _owned(root, task_state["folder"])
    task_path = folder / "TASK.json"
    if not task_path.exists():
        return None
    manifest.add(task_path, "alpha_current_task")
    _, task = _json(task_path)
    if (task.get("task_id") != task_id or task.get("index") != parent["index"]
            or task.get("target_path") != task_state["target_path"]):
        raise ValueError("Current alpha task identity differs")
    base_path, parent_path = _owned(root, task["base_file"]), _owned(root, task["parent_file"])
    manifest.add(base_path, "alpha_current_base", task["input_sha256"])
    manifest.add(parent_path, "alpha_current_parent", task["parent_sha256"])
    if _json(parent_path)[1] != parent:
        raise ValueError("Current alpha task parent differs from anchor")
    base, paid = pm.migration(base_path, bp, parent, task.get("migration_file"))
    structure = pm.extension(anchor, base)
    manifest.migration(paid, "alpha_current_base")
    return base_path, {"task_file": str(task_path.relative_to(root)),
                       "input_migration": paid, "anchor_extension": structure}


def _compose(index, root, state, pm, bp):
    """Dependency-explicit core; bounded fake tests need no frozen math imports."""
    folders = [t["folder"] for t in state["tasks"].values() if int(t["index"]) == index and "folder" in t]
    snapshot = _InputSnapshot(root, folders)
    paid = _PaidChecks(pm, snapshot)
    token = _ACTIVE.set(snapshot)
    try:
        receipt = _compose_snapshot(index, root, state, paid, bp)
        snapshot.ensure_unchanged()
        receipt["composition_cache"] = {"scope": "ONE_COMPOSITION_ONLY", **snapshot.stats,
                                        "every_original_target_binding_checked": True,
                                        "worker_projection_payloads_released_per_target": True,
                                        "immutable_input_stat_identities_rechecked_at_completion": True}
        return receipt
    finally:
        _ACTIVE.reset(token)


def _compose_snapshot(index, root, state, pm, bp):
    manifest = _Manifest(root)
    anchor_record_path = root / "anchors" / str(index) / "ANCHOR.json"
    manifest.add(anchor_record_path, "original_anchor_record")
    _, ar = _json(anchor_record_path)
    if ar.get("index") != index:
        raise ValueError("Original anchor index differs")
    anchor_path, parent_path = _owned(root, ar["anchor_base_file"]), _owned(root, ar["parent_file"])
    anchor_sha = manifest.add(anchor_path, "original_anchor")
    parent_sha = manifest.add(parent_path, "original_parent")
    _, parent = _json(parent_path)
    if parent.get("index") != index:
        raise ValueError("Original parent index differs")
    anchor, paid_anchor = pm.migration(anchor_path, bp, parent, ar.get("migration_file"))
    manifest.migration(paid_anchor, "paid_original_anchor")
    targets = sorted(pm.old_open_paths(anchor["tree"]))
    declared = ar.get("original_open_paths")
    if (not isinstance(declared, list) or any(not isinstance(p, str) or any(c not in "01" for c in p) for p in declared)
            or len(set(declared)) != len(declared) or sorted(declared) != targets
            or any(q.startswith(p) for p, q in zip(targets, targets[1:]))):
        raise ValueError("Original OPEN paths are not a complete prefix-free partition")
    if not targets:
        raise ValueError("Alpha composition requires an original OPEN anchor")
    selected = {}
    for task_id, task in sorted(state["tasks"].items()):
        if int(task["index"]) != index:
            continue
        target = task["target_path"]
        if target not in targets or target in selected or task.get("task_id", task_id) != task_id:
            raise ValueError("Original target is absent, duplicated, or misowned")
        selected[target] = (task_id, task)
    if set(selected) != set(targets):
        raise ValueError("RUN_STATE does not account for every original target exactly once")
    rows = []
    for target in targets:
        task_id, task = selected[target]
        status = task["status"]
        row = {"target_path": target, "task_id": task_id, "observed_task_status": status}
        if status == "CLOSED":
            folder = _owned(root, task["folder"])
            # Capture the task bytes around the paid checker as well as its
            # immutable result/final hashes, so a concurrent task rewrite is
            # rejected instead of producing a mixed evidence manifest.
            task_sha = manifest.add(folder / "TASK.json", "closed_worker_task")
            subtree, evidence = pm.check_worker_result(task, anchor, parent, bp, task_id)
            if not evidence["closed"] or pm.counts(subtree).get("O", 0):
                raise ValueError("Closed worker evidence is not complete")
            manifest.add(folder / "TASK.json", "closed_worker_task", task_sha)
            _, worker_task = _json(folder / "TASK.json")
            manifest.add(worker_task["base_file"], "closed_worker_input", worker_task["input_sha256"])
            manifest.add(worker_task["parent_file"], "closed_worker_parent", worker_task["parent_sha256"])
            manifest.add(folder / "RESULT.json", "paid_closed_worker_receipt", evidence["result_file_sha256"])
            manifest.add(folder / "final.json", "closed_worker_projection", evidence["projected_file_sha256"])
            manifest.migration(evidence["input_migration"], "closed_worker_base")
            row.update(status="CLOSED", closed=True, evidence=evidence,
                       independent_mathematical_receipt_reused=True)
        elif status == "COVERED_BY_PRODUCTION":
            covered = _owned(root, task["covered_base_file"])
            source, paid = pm.migration(covered, bp, parent, task.get("covered_migration_file"))
            structure = pm.extension(anchor, source)
            subtree = pm.at(source["tree"], target)
            counted = pm.counts(subtree)
            if counted.get("O", 0):
                raise ValueError("Production-covered target still contains OPEN")
            manifest.migration(paid, "paid_production_cover")
            row.update(status="COVERED_BY_PRODUCTION", closed=True,
                       evidence={"input_migration": paid, "anchor_extension": structure,
                                 "target_counts": counted, "subtree_sha256": pm.digest(subtree)},
                       independent_mathematical_receipt_reused=True)
        elif status == "COVERED_BY_ALPHA":
            ref = task.get("alpha_coverage")
            evidence = verify_alpha_evidence(root, bp, parent_path, ref, anchor_path, target)
            # The anchor path list above guarantees this target really is O.
            manifest.add(evidence["cut_certificate_file"], "independent_alpha_cut", evidence["cut_certificate_sha256"])
            manifest.add(evidence["acceptance_file"], "paid_independent_alpha_acceptance", evidence["acceptance_sha256"])
            current = _task_input(root, pm, bp, parent, anchor, task_id, task, manifest)
            if current is not None:
                base_path, input_ref = current
                current_node = pm.at(_json(base_path)[1]["tree"], target)
                if current_node["terminal"] == {"kind": "O"}:
                    current_evidence = verify_alpha_evidence(root, bp, parent_path, ref, base_path, target)
                    evidence["current_task_base"] = {**input_ref, "coverage_binding": current_evidence["coverage_binding"]}
                else:
                    evidence["current_task_base"] = {**input_ref, "current_target_kind": current_node["terminal"]["kind"],
                        "domain_transferred_by_exact_extension": True,
                        "basis": "ACCEPTED_ALPHA_COVERS_ORIGINAL_ANCHOR_O_AND_CURRENT_BASE_EXTENDS_ANCHOR"}
            else:
                evidence["current_task_base"] = {"status": "NO_TASK_INPUT_CREATED", "anchor_binding_sufficient": True}
            row.update(status="COVERED_BY_ALPHA", closed=True, evidence=evidence,
                       independent_mathematical_receipt_reused=True)
        else:
            # In particular ALPHA_RETIRING is not paid coverage until the bridge
            # has completed the explicit task-status transition.
            row.update(status="OPEN", closed=False)
        rows.append(row)
        _ACTIVE.get().finish_target()
    closed = sum(row["closed"] for row in rows)
    open_paths = [row["target_path"] for row in rows if not row["closed"]]
    if closed + len(open_paths) != len(targets):
        raise ValueError("Incomplete original target coverage accounting")
    source_signature = _digest({"index": index, "anchor_sha256": anchor_sha,
                                "original_open_paths": targets, "targets": rows})
    coverage_counts = {kind: sum(row["status"] == kind for row in rows)
                       for kind in ("CLOSED", "COVERED_BY_PRODUCTION", "COVERED_BY_ALPHA", "OPEN")}
    return {"schema": SCHEMA, "status": ACCEPTED if not open_paths else "OPEN", "index": index,
            "epoch": time.time(), "rule": "RHO5_PAID_ANCHOR_ALPHA_COVER_COMPOSITION_V1",
            "deep_rule_identity": bp.rule_hash(), "alpha_rule_identity": _peer(root, "alpha_cover").rule_identity(),
            "source_signature": source_signature, "anchor_file": str(anchor_path.relative_to(root)),
            "anchor_sha256": anchor_sha, "parent_file": str(parent_path.relative_to(root)),
            "parent_sha256": parent_sha, "anchor_input_migration": paid_anchor,
            "original_open_paths": targets, "original_open_paths_sha256": _digest(targets),
            "total_original_targets": len(targets), "covered_targets": closed, "open_targets": len(open_paths),
            "coverage_counts": coverage_counts,
            "still_open_paths": open_paths, "targets": rows, "evidence_manifest": manifest.rows(),
            "new_mathematical_replay_performed": False, "paid_old_mathematics_reused": True,
            "independent_alpha_mathematics_receipts_reused": bool(coverage_counts["COVERED_BY_ALPHA"]),
            "whole_root_credit": False, "whole_root_accepted": False, "old_frozen_rule_acceptance": False,
            "old_coverage_modified": False, "mixed_old_new_tree_created": False,
            "acceptance_scope": "ALL_ORIGINAL_OPEN_DOMAINS_PLUS_ALREADY_PAID_ANCHOR_COMPLEMENT"}


def _atomic(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_name(path.name + ".tmp." + str(os.getpid()))
    with temp.open("x") as f:
        json.dump(value, f, ensure_ascii=False, sort_keys=True, indent=2)
        f.write("\n")
        f.flush()
        os.fsync(f.fileno())
    os.replace(temp, path)


def accept_parent(index, root=None, state=None):
    """Write only parents/<index>/ALPHA_COMPOSITE_RESULT.json; fail closed."""
    root = Path(root or ROOT).resolve()
    index = int(index)
    pm, ac = _peer(root, "parents_merger"), _peer(root, "alpha_cover")
    _, config = _json(root / "CONFIG.json")
    ac.configure(_owned(root, config["alpha_support_directory"]))
    bp = pm.load_protocol(root)
    if state is None:
        _, state = _json(root / "RUN_STATE.json")
    receipt = _compose(index, root, state, pm, bp)
    receipt["composition_implementation_sha256"] = _sha(Path(__file__))
    # Pin the receipt-composition code, the original verifier package manifest,
    # and the small alpha support files without replaying any mathematics.
    source_manifest = _Manifest(root)
    for name in ("alpha_parent_cover.py", "parents_merger.py", "deep_math.py", "alpha_cover.py",
                 "runtime/DEEP500_MANIFEST.json", "CONFIG.json"):
        source_manifest.add(name, "acceptance_runtime")
    support = _owned(root, config["alpha_support_directory"])
    for rel, expected in ac.PINNED.items():
        source_manifest.add(support / rel, "pinned_alpha_support", expected)
    receipt["evidence_manifest"].extend(source_manifest.rows())
    receipt["evidence_manifest"].sort(key=lambda row: row["file"])
    # File hashes authenticate every proof/receipt input; the selected task-state
    # snapshot is included so unrelated active tasks need not stop changing.
    receipt["observed_parent_task_state"] = {k: v for k, v in state["tasks"].items() if int(v["index"]) == index}
    receipt["observed_parent_task_state_sha256"] = _digest(receipt["observed_parent_task_state"])
    receipt["evidence_manifest_sha256"] = _digest(receipt["evidence_manifest"])
    _atomic(root / "parents" / str(index) / "ALPHA_COMPOSITE_RESULT.json", receipt)
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("index", type=int)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    sys.setrecursionlimit(10000)
    sys.dont_write_bytecode = True
    began = time.time()
    try:
        answer = accept_parent(args.index, args.root)
        print(json.dumps({k: answer[k] for k in ("status", "index", "total_original_targets", "covered_targets", "open_targets", "source_signature")}), flush=True)
    except BaseException:
        _atomic(args.root.resolve() / "parents" / str(args.index) / "ALPHA_COMPOSITE_ERROR.json",
                {"status": "REJECTED", "index": args.index, "started_epoch": began, "epoch": time.time(),
                 "error": traceback.format_exc(), "old_outputs_preserved": True,
                 "whole_root_credit": False, "automatic_retry": False})
        raise


if __name__ == "__main__":
    main()
