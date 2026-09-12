"""Independent, source-bound alpha safety; never an old V44 A/H/C terminal.

Call configure(B14_DIRECTORY) once. It privately loads four hash-pinned pure
modules without changing sys.path or sys.modules. No discoverer/optimizer runs.
make_cut returns JSON data; write it atomically, then verify_cut accepts its
Path/bytes to bind the receipt to actual original bytes. coverage_binding is
STRUCTURAL ONLY: pair it with a verify_cut receipt before granting any closure.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import builtins
import copy
import hashlib
import json
import types

RULE = "RHO5_B14_V51_ALPHA_COVER_V1"
CUT_SCHEMA = "RHO5_SOURCE_BOUND_ALPHA_CUT_V1"
PORT_RULE = "RHO5_EXACT_SYMMETRY_ALPHA_PORT_V1"
ALPHA_LOWER = Q("4.13251707863247285422334685327737126995")
V36_RADIUS = Q(1, 1250)
R_RADIUS = Q(3, 1000)
PINNED = {
    "support/exact_interval.py": "4d42cc42c683bdfd5aff25cb4307d43a9edb3062c2b8ed14c992c722168bea39",
    "support/structural_rules.py": "48eebc9e1172eadf1ef8e876c148b5d11014a3ad25ee78ad1171477a6002afb1",
    "transport_local.py": "3c1fdc2dd64ff0399abd3596213a08fba62cd865ecc2e9a1def3a65e38bdb6f7",
    "alpha_port.py": "51b378f95d23529e017a2057977cfa9a7eed4ee6bca081fad9ddee1315186c43",
    "centers.json": "5f43ec82bd73090ffb5f7508ce8705eab5d9c8342303066b029dc9322021004b",
    "accepted_inputs/V36_THEOREMS.md": "3e11a0804b8556249bf6e51f0971a2b803244e5f7558f4676645e7f5006b12af",
    "accepted_inputs/V43_THEOREMS.md": "c8a64b2ad220abaced72600eeea4ebef36622d8ae4f19addea0205acd788fa2f",
    "accepted_inputs/ALPHA_EXACT.json": "9af09b9d6e584bba2a7cef7e9e3993f128fbc90744335eb0c22c8b11e0226959",
}
_MATH = None
_CACHE_SEAL = object()


def encoded(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def digest(obj):
    return hashlib.sha256(encoded(obj)).hexdigest()


def configure(b14_directory):
    """Load pinned pure code with private import resolution, leaving production imports alone."""
    global _MATH
    root = Path(b14_directory).resolve()
    blobs = {}
    for rel, expected in PINNED.items():
        blobs[rel] = (root / rel).read_bytes()
        if hashlib.sha256(blobs[rel]).hexdigest() != expected:
            raise ValueError("Changed B14 dependency: " + rel)
    modules = {}
    real_import = builtins.__import__

    def private_import(name, globals=None, locals=None, fromlist=(), level=0):
        if not level and name in modules:
            return modules[name]
        if not level and name in ("exact_interval", "structural_rules", "transport_local", "alpha_port"):
            raise ImportError("Private alpha dependency not yet loaded: " + name)
        return real_import(name, globals, locals, fromlist, level)

    for name, rel in (("exact_interval", "support/exact_interval.py"),
                      ("structural_rules", "support/structural_rules.py"),
                      ("transport_local", "transport_local.py"), ("alpha_port", "alpha_port.py")):
        module = types.ModuleType("_rho5_private_b14_" + name)
        module.__file__ = str(root / rel)
        module.__dict__["__builtins__"] = {**vars(builtins), "__import__": private_import}
        exec(compile(blobs[rel], module.__file__, "exec"), module.__dict__)
        modules[name] = module
    centers = [[_rational(v) for v in row] for row in json.loads(blobs["centers.json"])]
    if len(centers) != 4 or any(len(row) != 24 for row in centers):
        raise ValueError("Malformed fixed centers")
    alpha_isolation = json.loads(blobs["accepted_inputs/ALPHA_EXACT.json"])["isolating_interval"]
    if ALPHA_LOWER > _rational(alpha_isolation["lower"]):
        raise ValueError("Direct height threshold exceeds the pinned alpha lower bound")
    _MATH = types.SimpleNamespace(root=root, modules=modules, centers=centers,
                                  centers_sha256=digest([[str(v) for v in c] for c in centers]))
    return {"rule": RULE, "rule_identity": rule_identity(), "centers_sha256": _MATH.centers_sha256,
            "dependencies": dict(PINNED), "production_imports_modified": False}


def _math():
    if _MATH is None:
        raise RuntimeError("Call alpha_cover.configure(B14_DIRECTORY) first")
    return _MATH


def _rational(value):
    if isinstance(value, (float, bool)):
        raise TypeError("Exact integer, fraction or rational string required")
    return Q(value)


def fixed_centers():
    return copy.deepcopy(_math().centers)


def _centers(centers):
    result = [[_rational(v) for v in row] for row in centers]
    if len(result) != 4 or any(len(row) != 24 for row in result) or result != _math().centers:
        raise ValueError("Centers differ from the fixed accepted V36/V43 centers")
    return result


def rule_identity():
    _math()
    return digest({"rule": RULE, "schema": CUT_SCHEMA, "port_rule": PORT_RULE,
                   "implementation_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   "dependencies": PINNED, "centers_sha256": _MATH.centers_sha256,
                   "alpha_lower": str(ALPHA_LOWER), "v36_radius": str(V36_RADIUS), "r_radius": str(R_RADIUS),
                   "semantic": "ALPHA_SAFE_OR_EXACT_INTERVAL_EMPTY_NOT_OLD_V44_TERMINAL"})


def _image(aux):
    if not isinstance(aux, (list, tuple)) or len(aux) != 24:
        raise ValueError("Expected the complete 24-coordinate image")
    if any(not isinstance(pair, (list, tuple)) or len(pair) != 2 for pair in aux):
        raise ValueError("Malformed interval image")
    return _math().modules["structural_rules"].image(aux)


def _representation_names():
    return ["T%dD%dS%s" % (t, d, "".join("+" if v == 1 else "-" for v in ss))
            for t, d in product((0, 1), repeat=2) for ss in product((-1, 1), repeat=3)]


def _representation(x, name):
    if name not in _representation_names():
        raise ValueError("Unknown finite physical representation")
    sr = _math().modules["structural_rules"]
    y = sr.transpose(x) if name[1] == "1" else x
    if name[3] == "1":
        y = sr.diagonal_swap(y)
    return sr.sign_rep(y, tuple(1 if c == "+" else -1 for c in name[5:]))


def _v36_scores(y, centers):
    sr = _math().modules["structural_rules"]
    interval = _math().modules["exact_interval"].I
    sig, tau = y["r"] - y["s"], y["r"] - y["t"]
    if sig.hi < 0 or tau.hi < 0:
        raise ValueError("No certified physical nonnegative-gap enclosure")
    # Nonnegative actual gaps are a premise of the complete physical B source.
    sig = interval(max(Q(0), sig.lo), sig.hi)
    tau = interval(max(Q(0), tau.lo), tau.hi)
    target = [y["k"], y["r"], -y["r"]] + [y[n] for n in sr.ORDER[4:23]] + [sig, tau]
    gap_sum = sig.hi + tau.hi
    result = []
    for j, center in enumerate(centers):
        distance = max(max(abs(v.lo - a), abs(v.hi - a)) for v, a in zip(target, center))
        result.append({"center": j, "distance": distance, "gap_sum": gap_sum,
                       "budget": distance + 3 * gap_sum})
    return result


def _port_header(method):
    return {"rule": PORT_RULE, "semantic": "ALPHA_SAFE", "method": method,
            "centers_sha256": _math().centers_sha256}


def _discover_v36(y, representation, centers):
    rows = _v36_scores(y, centers)
    best = min(rows, key=lambda r: (r["budget"], r["center"]))
    if best["budget"] < V36_RADIUS:
        return {**_port_header("V36_FULL_GAP"), "representation": representation, "center": best["center"]}
    return None


def _discover_r(y, representation, centers):
    tl = _math().modules["transport_local"]
    branches = []
    for name, z in tl.sorted_branches(y):
        target, ell, _ = tl.sorted_R(z)
        budgets = [max(max(abs(v.lo - a), abs(v.hi - a)) for v, a in zip(target, center[:22]))
                   + tl.KAPPA[j] * ell.hi for j, center in enumerate(centers)]
        j = min(range(4), key=lambda k: (budgets[k], k))
        if budgets[j] > R_RADIUS:
            return None
        branches.append({"branch": name, "center": j})
    return {**_port_header("B14_SORTED_R"), "representation": representation, "branches": branches}


def discover_port(aux, centers):
    """Finite exact proposals: direct height, V51 T0/T1 V36, then all V36/R representations."""
    centers = _centers(centers)
    x = _image(aux)
    if x["F"].hi <= ALPHA_LOWER:
        return _port_header("DIRECT_HEIGHT")
    priority = ["T1D0S+++", "T1D0S++-"]  # V51 T0, then V51 T1
    for name in priority:
        try:
            hit = _discover_v36(_representation(x, name), name, centers)
            if hit is not None:
                return hit
        except (ValueError, ZeroDivisionError):
            pass
    for name in _representation_names():
        try:
            y = _representation(x, name)
        except (ValueError, ZeroDivisionError):
            continue
        for discover in (_discover_v36, _discover_r):
            try:
                hit = discover(y, name, centers)
                if hit is not None:
                    return hit
            except (ValueError, ZeroDivisionError):
                # A broad interval failing a physical denominator test is OPEN.
                continue
    return None


def verify_port(aux, port, centers):
    """Recompute the selected exact representation and ALL required sorted branches."""
    centers = _centers(centers)
    x = _image(aux)
    if not isinstance(port, dict):
        raise ValueError("Malformed alpha port")
    method = port.get("method")
    header = _port_header(method)
    if any(port.get(k) != v for k, v in header.items()):
        raise ValueError("Wrong alpha rule, semantics or fixed centers")
    if method == "DIRECT_HEIGHT":
        if set(port) != set(header) or x["F"].hi > ALPHA_LOWER:
            raise ValueError("False direct alpha height")
        detail = {"height_upper": str(x["F"].hi), "certified_alpha_lower": str(ALPHA_LOWER)}
    elif method == "V36_FULL_GAP":
        if set(port) != set(header) | {"representation", "center"} or type(port["center"]) is not int:
            raise ValueError("Malformed V36 port")
        if not 0 <= port["center"] < 4:
            raise ValueError("Invalid V36 center")
        row = _v36_scores(_representation(x, port["representation"]), centers)[port["center"]]
        if row["budget"] >= V36_RADIUS:
            raise ValueError("V36 strict full-gap budget failed")
        detail = {k: str(v) if isinstance(v, Q) else v for k, v in row.items()}
        detail["margin"] = str(V36_RADIUS - row["budget"])
    elif method == "B14_SORTED_R":
        if set(port) != set(header) | {"representation", "branches"}:
            raise ValueError("Malformed sorted R port")
        # Pinned verifier recomputes representations, sorted coverage, all four
        # center bindings, coefficients, distances and loss; cached budgets absent.
        proposal = {"rule": "B14_SYMMETRY_ALPHA_V1", "semantic": "ALPHA_SAFE",
                    "representation": port["representation"], "branches": port["branches"],
                    "centers_sha256": port["centers_sha256"]}
        detail = _math().modules["alpha_port"].verify_conditional(aux, proposal, centers)
    else:
        raise ValueError("Unknown alpha safety method")
    return {"rule": PORT_RULE, "status": "ALPHA_SAFE", "method": method,
            "source_image_sha256": digest(aux), "detail": detail,
            "does_not_prove_gamma_infeasibility": True}


def _json_source(source, require_raw=False):
    if isinstance(source, (str, Path)):
        raw = Path(source).read_bytes()
        data = json.loads(raw)
    elif isinstance(source, bytes):
        raw, data = source, json.loads(source)
    elif isinstance(source, tuple) and len(source) == 2 and isinstance(source[0], bytes):
        raw, data = source
        if json.loads(raw) != data:
            raise ValueError("Raw and parsed JSON sources differ")
    elif isinstance(source, dict) and not require_raw:
        raw, data = None, source
    else:
        raise TypeError("Original JSON Path/bytes/(rawbytes, parsed) required")
    if not isinstance(data, dict):
        raise ValueError("Expected a JSON object")
    return data, hashlib.sha256(raw).hexdigest() if raw is not None else None


def _binary_path(path):
    if not isinstance(path, str) or len(path) > 500 or any(c not in "01" for c in path):
        raise ValueError("Invalid local actual-image path")


def _validate_waves(waves):
    if not isinstance(waves, list) or len(waves) > 128 or any(not isinstance(w, list) for w in waves):
        raise ValueError("Invalid original rational-wave list")


def _cut_metadata(bp, parent_source, certificate):
    parent, parent_raw = _json_source(parent_source, require_raw=True)
    cut, cut_raw = _json_source(certificate)
    if set(cut) != {"schema", "rule", "rule_identity", "source", "cut_path", "lineage", "terminal"}:
        raise ValueError("Malformed independent cut envelope")
    if (cut["schema"] != CUT_SCHEMA or cut["rule"] != RULE or cut["rule_identity"] != rule_identity()):
        raise ValueError("Wrong independent cut rule identity")
    source = cut["source"]
    if not isinstance(source, dict) or set(source) != {"parent_raw_sha256", "parent_binding", "profile"}:
        raise ValueError("Malformed parent source binding")
    expect = bp.binding(parent)
    if source["parent_raw_sha256"] != parent_raw or source["parent_binding"] != expect:
        raise ValueError("Wrong original parent bytes or frozen U41/box binding")
    bp.db.validate_profile(source["profile"])
    _binary_path(cut["cut_path"])
    lineage = cut["lineage"]
    if not isinstance(lineage, list) or len(lineage) != len(cut["cut_path"]) + 1:
        raise ValueError("Incomplete root-to-cut lineage")
    for depth, node in enumerate(lineage):
        fields = {"waves"} if depth == len(cut["cut_path"]) else {"waves", "axis"}
        if not isinstance(node, dict) or set(node) != fields:
            raise ValueError("Incomplete original waves or ancestor axis")
        _validate_waves(node["waves"])
        if "axis" in node and (type(node["axis"]) is not int or not 0 <= node["axis"] < 24):
            raise ValueError("Ancestor split is not an actual image coordinate")
    terminal = cut["terminal"]
    if not isinstance(terminal, dict):
        raise ValueError("Malformed cut terminal")
    if terminal.get("kind") == "ALPHA_SAFE":
        if set(terminal) != {"kind", "port"}:
            raise ValueError("Malformed independent alpha terminal")
    elif terminal.get("kind") == "EXACT_SUBTREE":
        if set(terminal) != {"kind", "tree"} or lineage[-1]["waves"] != []:
            raise ValueError("Mixed subtree needs an unchanged cut inbox and empty cut-local lineage waves")
    elif terminal != {"kind": "EMPTY_INTERVAL"}:
        raise ValueError("No old A/H/C/O terminal is accepted by this new rule")
    return parent, parent_raw, cut, cut_raw, expect


def make_cut(bp, parent_source, profile, cut_path, lineage, terminal):
    parent, parent_raw = _json_source(parent_source, require_raw=True)
    value = {"schema": CUT_SCHEMA, "rule": RULE, "rule_identity": rule_identity(),
             "source": {"parent_raw_sha256": parent_raw, "parent_binding": bp.binding(parent), "profile": profile},
             "cut_path": cut_path, "lineage": copy.deepcopy(lineage), "terminal": copy.deepcopy(terminal)}
    _cut_metadata(bp, parent_source, value)
    return value


class _VerifiedCache:
    __slots__ = ("seal", "value")
    def __init__(self, value):
        self.seal, self.value = _CACHE_SEAL, copy.deepcopy(value)


def _cache_result(cache, key, compute):
    entry = cache.get(key) if cache is not None else None
    if isinstance(entry, _VerifiedCache) and entry.seal is _CACHE_SEAL:
        return copy.deepcopy(entry.value), True
    value = compute()
    if cache is not None:
        cache[key] = _VerifiedCache(value)
    return copy.deepcopy(value), False


def _checked_contract(bp, inbox, waves, profile, cache, namespace):
    key = namespace + ("node", digest({"inbox": inbox, "waves": waves, "profile": profile}))
    def compute():
        out = bp.db.common_contract(copy.deepcopy(inbox), profile=profile)
        for wave in waves:
            out = bp.db.apply_wave(out, wave, profile=profile, cross_check=True)
        return out
    return _cache_result(cache, key, compute)


def _verify_mixed_subtree(bp, inbox, tree, profile, centers, cache, namespace, initial_depth):
    """One complete exact cover with independent N alpha leaves; no O accepted."""
    counts, cache_hits = {}, 0
    pending = [(inbox, tree, initial_depth)]
    while pending:
        before, node, depth = pending.pop()
        if depth > 500:
            raise ValueError("Mixed proof exceeds the depth-500 protocol")
        terminal = _base_node(node)
        out, hit = _checked_contract(bp, before, node["waves"], profile, cache, namespace)
        cache_hits += int(hit)
        kind = terminal.get("kind")
        counts["nodes"] = counts.get("nodes", 0) + 1
        counts["maxdepth"] = max(counts.get("maxdepth", 0), depth)
        counts["new_waves"] = counts.get("new_waves", 0) + len(node["waves"])
        counts["new_bounds"] = counts.get("new_bounds", 0) + sum(map(len, node["waves"]))
        if kind == "I":
            if terminal != {"kind": "I"} or out["status"] != "EMPTY":
                raise ValueError("False interval leaf in mixed cover")
        elif kind == "O":
            raise ValueError("Unpaid O cannot complete an alpha subtree")
        else:
            if out["status"] != "BOUNDED":
                raise ValueError("Only I can receive a propagated empty image")
            if kind == "N":
                if set(terminal) != {"kind", "port"}:
                    raise ValueError("Malformed independent N alpha leaf")
                verify_port(out["aux_image"], terminal["port"], centers)
            elif kind == "A":
                if terminal != {"kind": "A"} or bp.fs.safe_port(out["aux_image"]) is None:
                    raise ValueError("False inherited A safe port")
            elif kind in ("C", "H"):
                rows, boxes = bp.db.rows_and_bounds(out["aux_image"], profile=profile)
                margin = bp.source.inherited.dual_margin(rows, boxes, terminal)
                weights = dict(terminal["weights"])
                dense = [sum(Q(weights[j]) * rows[j][0].get(i, Q(0)) for j in weights)
                         for i in range(len(boxes))]
                rhs = sum(Q(w) * rows[j][1] for j, w in weights.items())
                if kind == "H":
                    dense[23] -= terminal["objective_weight"]
                independent = rhs - sum(dense[i] * (b.lo if dense[i] >= 0 else b.hi)
                                        for i, b in enumerate(boxes))
                if kind == "H":
                    independent -= terminal["objective_weight"] * bp.fs.ALPHA
                if independent != margin:
                    raise ValueError("Dense/sparse dual mismatch in mixed cover")
                if (kind == "C" and margin >= 0) or (kind == "H" and margin > 0):
                    raise ValueError("Failed exact inherited dual leaf")
            elif kind == "S":
                axis = terminal["axis"]
                box = copy.deepcopy(out["aux_image"])
                lo, hi = map(_rational, box[axis]); mid = (lo + hi) / 2
                if not lo < mid < hi:
                    raise ValueError("Degenerate mixed-cover midpoint")
                left, right = copy.deepcopy(box), copy.deepcopy(box)
                left[axis][1], right[axis][0] = str(mid), str(mid)
                pending.append(({"status": "BOUNDED", "aux_image": right}, terminal["right"], depth + 1))
                pending.append(({"status": "BOUNDED", "aux_image": left}, terminal["left"], depth + 1))
            else:
                raise ValueError("Unknown leaf in mixed exact cover")
        counts[kind] = counts.get(kind, 0) + 1
    splits = counts.get("S", 0)
    if counts["nodes"] != 2 * splits + 1 or sum(counts.get(k, 0) for k in ("I", "C", "H", "A", "N")) != splits + 1:
        raise ValueError("Incomplete mixed binary cover")
    status = "ALPHA_SAFE" if any(counts.get(k, 0) for k in ("A", "H", "N")) else "EMPTY_INTERVAL"
    return status, counts, cache_hits


def verify_cut(bp, parent_source, certificate_source, centers, prefix_cache=None):
    """Independent source-to-cut replay, exact cross checks, and actual-byte receipt.

    A shared in-memory prefix_cache also reuses verified node computations.
    It accepts only entries produced by this verifier, never serialized boxes.
    """
    centers = _centers(centers)
    if ALPHA_LOWER > _rational(bp.fs.ALPHA):
        raise ValueError("Direct alpha lower bound exceeds frozen protocol ALPHA")
    if hasattr(bp.fs, "CENTERS") and [[_rational(v) for v in c] for c in bp.fs.CENTERS] != centers:
        raise ValueError("Frozen protocol centers differ from pinned V36/V43 centers")
    _, certificate_raw = _json_source(certificate_source, require_raw=True)
    parent, parent_raw, cut, _, expect = _cut_metadata(bp, parent_source, certificate_source)
    profile, lineage = cut["source"]["profile"], cut["lineage"]
    protocol_identity = expect["rule_identity"]
    namespace = (RULE, rule_identity(), id(bp), protocol_identity)
    def checked_prefix():
        return bp.prefix_image(parent, cross_check=True)
    (inbox, prefix_receipt), prefix_hit = _cache_result(
        prefix_cache, namespace + ("prefix", parent_raw), checked_prefix)
    node_hits = 0
    for depth, node in enumerate(lineage):
        if depth == len(cut["cut_path"]) and cut["terminal"]["kind"] == "EXACT_SUBTREE":
            # Its root supplies the actual waves/common_contract exactly once.
            out = inbox
            break
        out, hit = _checked_contract(bp, inbox, node["waves"], profile, prefix_cache, namespace)
        node_hits += int(hit)
        if depth == len(cut["cut_path"]):
            break
        if out["status"] != "BOUNDED":
            raise ValueError("Empty image before declared cut; no subsequent split is valid")
        axis = node["axis"]
        box = copy.deepcopy(out["aux_image"])
        lo, hi = map(_rational, box[axis])
        mid = (lo + hi) / 2
        if not lo < mid < hi:
            raise ValueError("Degenerate actual-image midpoint")
        box[axis][1 if cut["cut_path"][depth] == "0" else 0] = str(mid)
        inbox = {"status": "BOUNDED", "aux_image": box}
    subtree_counts = None
    if cut["terminal"]["kind"] == "EXACT_SUBTREE":
        status, subtree_counts, hits = _verify_mixed_subtree(
            bp, out, cut["terminal"]["tree"], profile, centers, prefix_cache, namespace, len(cut["cut_path"]))
        node_hits += hits
        port_receipt, image_hash = None, digest(out["aux_image"])
    elif cut["terminal"]["kind"] == "EMPTY_INTERVAL":
        if out["status"] != "EMPTY":
            raise ValueError("False exact interval emptiness")
        status, port_receipt, image_hash = "EMPTY_INTERVAL", None, None
    else:
        if out["status"] != "BOUNDED":
            raise ValueError("Only interval emptiness may receive an empty source")
        port_receipt = verify_port(out["aux_image"], cut["terminal"]["port"], centers)
        status, image_hash = "ALPHA_SAFE", digest(out["aux_image"])
    return {"schema": "RHO5_SOURCE_BOUND_ALPHA_CUT_ACCEPTANCE_V1", "rule": RULE,
            "rule_identity": rule_identity(), "status": status, "mathematical_acceptance": True,
            "mathematical_replay_performed": True, "independent_verifier": True,
            "certificate_sha256": certificate_raw, "certificate_object_sha256": digest(cut),
            "parent_raw_sha256": parent_raw, "parent_binding": expect, "profile": profile,
            "parent_index": parent["index"], "cut_path": cut["cut_path"],
            "source_image_sha256": image_hash, "port_acceptance": port_receipt,
            "terminal_kind": cut["terminal"]["kind"], "subtree_counts": subtree_counts,
            "prefix_cache_hit": prefix_hit, "verified_node_cache_hits": node_hits,
            "lineage_nodes": len(lineage), "cross_check": True,
            "does_not_prove_gamma_infeasibility": status == "ALPHA_SAFE",
            "old_frozen_rule_acceptance": False, "whole_parent_closed": False}


def _base_node(node):
    if not isinstance(node, dict) or set(node) != {"waves", "terminal"}:
        raise ValueError("Malformed original source node")
    _validate_waves(node["waves"])
    term = node["terminal"]
    if not isinstance(term, dict):
        raise ValueError("Malformed original terminal")
    if term.get("kind") == "S":
        if set(term) != {"kind", "axis", "left", "right"} or type(term["axis"]) is not int or not 0 <= term["axis"] < 24:
            raise ValueError("Malformed actual-image source split")
    return term


def coverage_binding(bp, parent_source, base_certificate, cut_certificate, target_path):
    """Bind an independently ACCEPTED cut to an original OPEN; no math replay.

    Returns None for non-covering/different ancestral domains. Raises for malformed
    identities. This structural receipt alone grants NO mathematical acceptance.
    Cut-local waves may differ: both are necessary constraints on the same domain.
    """
    parent, parent_raw, cut, cut_raw, expect = _cut_metadata(bp, parent_source, cut_certificate)
    base, base_raw = _json_source(base_certificate)
    if set(base) != set(expect) | {"profile", "tree"} or any(base.get(k) != v for k, v in expect.items()):
        raise ValueError("Original task base is not bound to this exact frozen protocol and parent")
    bp.db.validate_profile(base["profile"])
    if base["profile"] != cut["source"]["profile"]:
        return None
    _binary_path(target_path)
    cut_path = cut["cut_path"]
    if not target_path.startswith(cut_path):
        return None
    node = base["tree"]
    for depth in range(len(target_path) + 1):
        term = _base_node(node)
        if depth < len(cut_path):
            ancestor = cut["lineage"][depth]
            if term.get("kind") != "S" or node["waves"] != ancestor["waves"] or term["axis"] != ancestor["axis"]:
                return None
        if depth == len(target_path):
            if term != {"kind": "O"}:
                return None
            break
        if term.get("kind") != "S":
            return None
        node = term["left" if target_path[depth] == "0" else "right"]
    return {"schema": "RHO5_ALPHA_CUT_ORIGINAL_OPEN_BINDING_V1", "rule": RULE,
            "rule_identity": rule_identity(), "status": "EXACT_ORIGINAL_OPEN_COVER_BINDING",
            "parent_raw_sha256": parent_raw, "parent_index": parent["index"], "profile": base["profile"],
            "target_path": target_path, "cut_path": cut_path,
            "base_certificate_sha256": base_raw, "cut_certificate_sha256": cut_raw,
            "cut_certificate_object_sha256": digest(cut),
            "source_binding_sha256": digest({"parent_binding": expect, "profile": base["profile"],
                "target_path": target_path, "ancestor_lineage": cut["lineage"][:-1]}),
            "cut_local_waves_may_differ": True, "target_was_original_open": True,
            "requires_independent_cut_acceptance": True, "mathematical_acceptance": False,
            "whole_parent_closed": False}
