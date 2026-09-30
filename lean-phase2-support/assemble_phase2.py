#!/usr/bin/env python3
"""Assemble frozen public RHO5 sources without running Lean or using the network.

Example (run from the downloaded dependency supplement directory):
  python3 assemble_phase2.py --base ../rho5-proof/lean \
    --phase2-zip ../RHO5_Lean_Phase2_B366_SOURCE_ONLY_v1.0.2.zip \
    --supplement . --manifest DEPENDENCY_MANIFEST.json \
    --manifest-sha256 <SHA256-from-the-release-manifest> \
    --output ../rho5-phase2-assembled

Add --verify-only to perform the same input-identity and static dependency checks
without writing an output project. Assembly is not compilation, axiom checking,
certificate-tree checking, or an unconditional proof of the paper. The generated
Lake configuration and aggregate entrypoint are explicitly NOT_LEAN_TESTED.
Requires Python 3.10+ and only the Python standard library.
"""

from __future__ import annotations

import argparse
import hashlib
import heapq
import json
import re
import sys
import zipfile
from pathlib import Path, PurePosixPath


PHASE2_ZIP_SHA256 = "3c4dcb433ad5af1deee9c2f18531e862110c62c501cdbe5c54ed2a9d06d97fc7"
BASE_MANIFEST_SHA256 = "979e87b4a43b33e5e0770b145f0be67ac0231e5461238ddeb45086649b94e269"
BASE_CONFIG_SHA256 = {
    "lakefile.toml": "bb06bd656723ce3c57074d9bf2c028540baaf87e43469cb186ac16ce4d35a358",
    "lean-toolchain": "54727eec5cba149c18842e6deb5c41b369d66455c93ce135d7d5347c782b2325",
    "lake-manifest.json": "6fa600a652ca1ef77814e08127d1078febb38e3018ed9f8b1c5683b92427b789",
}
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
KNOWN_EXTERNAL_NAMESPACES = {"Mathlib", "Lean", "Init", "Std", "Batteries"}
# Commands and modifiers that end an import header. Their source lines must not
# be mistaken for a list of import module names merely because they contain
# identifiers. This inventory deliberately accepts single-line import headers;
# bare imports or ambiguous module-only continuation lines are rejected below.
LEAN_COMMAND_STARTS = {
    "import", "prelude", "module", "namespace", "section", "end", "open",
    "export", "variable", "variables", "universe", "universes", "set_option",
    "attribute", "local", "scoped", "protected", "private", "public", "meta",
    "noncomputable", "unsafe", "partial", "opaque", "def", "abbrev", "theorem",
    "lemma", "example", "instance", "class", "structure", "inductive",
    "coinductive", "syntax", "macro", "macro_rules", "elab", "elab_rules",
    "mutual", "where", "deriving", "initialize", "builtin_initialize", "axiom",
    "constant", "constants", "notation", "infix", "infixl", "infixr", "prefix",
    "postfix", "declare_syntax_cat", "register_option", "register_builtin_option",
    "run_cmd", "include", "omit", "set_library_suggestions", "simproc_decl",
    "simproc", "builtin_simproc", "builtin_simproc_decl", "initialize_simps_projections",
}


class AssemblyError(Exception):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def checked_hash(data: bytes, expected: str, label: str) -> None:
    if not isinstance(expected, str) or not SHA256.fullmatch(expected):
        raise AssemblyError(f"Invalid SHA-256 for {label}")
    actual = sha256(data)
    if actual != expected:
        raise AssemblyError(f"SHA-256 mismatch for {label}: expected {expected}, got {actual}")


def safe_relative(path: str) -> PurePosixPath:
    p = PurePosixPath(path)
    if not path or p.is_absolute() or ".." in p.parts or "\\" in path:
        raise AssemblyError(f"Unsafe relative path: {path!r}")
    return p


def local_bytes(root: Path, relative: str) -> bytes:
    p = root.joinpath(*safe_relative(relative).parts)
    if not p.is_file() or p.is_symlink():
        raise AssemblyError(f"Missing or symlinked input file: {p}")
    try:
        p.resolve().relative_to(root.resolve())
    except ValueError as e:
        raise AssemblyError(f"Input escapes its source root: {p}") from e
    return p.read_bytes()


def module_path(module: str) -> str:
    if not MODULE.fullmatch(module) or not (module == "Rho5" or module.startswith("Rho5.")):
        raise AssemblyError(f"Unsupported Rho5 module name: {module!r}")
    return module.replace(".", "/") + ".lean"


def module_from_path(path: str) -> str:
    p = safe_relative(path)
    if p.suffix != ".lean" or p.parts[0] != "Rho5":
        raise AssemblyError(f"Not a canonical Rho5 source path: {path!r}")
    module = str(p.with_suffix("")).replace("/", ".")
    module_path(module)
    return module


def parse_sha_manifest(text: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for lineno, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        if not match:
            raise AssemblyError(f"Malformed SHA-256 manifest line {lineno}")
        digest, path = match.groups()
        safe_relative(path)
        if path in result:
            raise AssemblyError(f"Duplicate SHA-256 manifest path: {path}")
        result[path] = digest
    return result


def strip_comments_and_strings(text: str) -> str:
    """Erase nested /- -/, line -- comments and escaped double-quoted strings.

    Newlines are preserved. This is a deliberately bounded import inventory
    lexer, not the Lean parser. Unsupported import syntax causes failure below.
    Apostrophes in Lean identifiers are preserved.
    """
    chars = list(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                chars[i:i + 2] = [" ", " "]
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                chars[i:i + 2] = [" ", " "]
                depth -= 1
                i += 2
            else:
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
        elif quoted:
            if text[i] == "\\" and i + 1 < len(text):
                chars[i] = " "
                if chars[i + 1] != "\n":
                    chars[i + 1] = " "
                i += 2
            else:
                if text[i] == '"':
                    quoted = False
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
        elif text.startswith("/-", i):
            chars[i:i + 2] = [" ", " "]
            depth = 1
            i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                chars[i] = " "
                i += 1
        elif text[i] == '"':
            chars[i] = " "
            quoted = True
            i += 1
        else:
            i += 1
    if depth or quoted:
        raise AssemblyError("Unterminated block comment or string in source inventory")
    return "".join(chars)


def source_imports(data: bytes, label: str) -> list[str]:
    try:
        text = strip_comments_and_strings(data.decode("utf-8"))
    except (UnicodeDecodeError, AssemblyError) as e:
        raise AssemblyError(f"Cannot inventory imports in {label}: {e}") from e
    imports: set[str] = set()
    lines = text.splitlines()
    header = re.compile(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\b(.*)$")
    for lineno, line in enumerate(lines):
        match = header.fullmatch(line)
        if not match:
            continue
        tokens = match.group(1).split()
        if not tokens or any(not MODULE.fullmatch(token) for token in tokens):
            raise AssemblyError(f"Unsupported import syntax in {label}: {match.group(0)!r}")
        # Fail closed instead of silently omitting a bare or multiline import.
        # Ordinary declarations such as `namespace Foo` or `noncomputable
        # section` are commands, not continuation modules, and remain accepted.
        for following in lines[lineno + 1:]:
            continuation = following.split()
            if not continuation:
                continue
            if (continuation[0] not in LEAN_COMMAND_STARTS
                    and all(MODULE.fullmatch(token) for token in continuation)):
                raise AssemblyError(
                    f"Unsupported multiline import continuation in {label}: {following!r}")
            break
        imports.update(tokens)
    return sorted(imports)


def add_source(sources: dict, module: str, data: bytes, origin: str) -> None:
    module_path(module)
    digest = sha256(data)
    if module in sources:
        old = sources[module]
        if old["sha256"] != digest:
            raise AssemblyError(f"Conflicting bytes for {module}: {old['origins']} versus {origin}")
        old["origins"].append(origin)
    else:
        sources[module] = {"data": data, "sha256": digest, "origins": [origin]}


def load_base(root: Path, sources: dict) -> dict:
    manifest_data = local_bytes(root, "SHA256SUMS")
    checked_hash(manifest_data, BASE_MANIFEST_SHA256, "frozen PhaseOne SHA256SUMS")
    entries = parse_sha_manifest(manifest_data.decode("utf-8"))
    for path, digest in sorted(entries.items()):
        data = local_bytes(root, path)
        checked_hash(data, digest, "PhaseOne " + path)
        if path.startswith("Rho5/") and path.endswith(".lean"):
            add_source(sources, module_from_path(path), data, "phaseone:" + path)
    config = {}
    for path, digest in BASE_CONFIG_SHA256.items():
        data = local_bytes(root, path)
        checked_hash(data, digest, "frozen PhaseOne " + path)
        config[path] = data
    return {"config": config, "verified_manifest_files": len(entries)}


def load_phase2(path: Path, sources: dict) -> tuple[list[str], dict]:
    archive_data = path.read_bytes()
    checked_hash(archive_data, PHASE2_ZIP_SHA256, "published B366 ZIP")
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        if len(names) != len(set(names)):
            raise AssemblyError("Duplicate ZIP member names")
        for name in names:
            safe_relative(name)
        manifest = json.loads(archive.read("evidence/PHASE2_LOC_MANIFEST_B366.json"))
        adopted = {e["module"]: e["sha256"] for e in manifest["candidate_modules"]
                   if e.get("formal_receipt_source_match") is True}
        supports = {e["module"]: e["source_sha256"]
                    for e in manifest["compiled_support_excluded_from_adopted_counts"]}
        if len(adopted) != 1452 or len(supports) != 4 or set(adopted) & set(supports):
            raise AssemblyError("Unexpected B366 adopted/support source counts")
        expected = {**adopted, **supports}
        source_members = {}
        archive_sha_manifest = parse_sha_manifest(
            archive.read("evidence/REVIEW3_SOURCE_SHA256SUMS.txt").decode("utf-8"))
        for name in names:
            if not name.endswith(".lean"):
                continue
            if name.startswith("lean_phase2/src/Rho5/"):
                relative = name[len("lean_phase2/src/"):]
            elif name.startswith("lean_phase2/Rho5/"):
                relative = name[len("lean_phase2/"):]
            else:
                raise AssemblyError("Unexpected source location in B366 archive: " + name)
            module = module_from_path(relative)
            if module not in expected or name not in archive_sha_manifest:
                raise AssemblyError("Unmanifested B366 source: " + name)
            data = archive.read(name)
            checked_hash(data, expected[module], "B366 " + module)
            checked_hash(data, archive_sha_manifest[name], "B366 member " + name)
            if module in source_members:
                raise AssemblyError("Duplicate normalized B366 module: " + module)
            source_members[module] = name
            add_source(sources, module, data, "b366:" + name)
        if set(source_members) != set(expected) or set(archive_sha_manifest) != set(source_members.values()):
            raise AssemblyError("B366 ZIP membership does not match exact manifest membership")
        evidence = {name: archive.read(name) for name in names
                    if not name.endswith(".lean") and not name.endswith("/")}
    return sorted(expected), {"evidence": evidence, "adopted_modules": 1452, "support_modules": 4}


def load_supplement(root: Path, manifest_path: Path, expected_digest: str, sources: dict) -> dict:
    data = manifest_path.read_bytes()
    checked_hash(data, expected_digest, "dependency manifest")
    manifest = json.loads(data)
    entries = manifest.get("sources")
    if not isinstance(entries, list):
        raise AssemblyError("Dependency manifest requires a sources array")
    seen = set()
    for entry in entries:
        module, path, digest = entry["module"], entry["path"], entry["sha256"]
        if module in seen:
            raise AssemblyError("Duplicate dependency manifest module: " + module)
        seen.add(module)
        source = local_bytes(root, path)
        checked_hash(source, digest, "dependency " + module)
        if not path.endswith(module_path(module)):
            raise AssemblyError("Dependency source path does not match module: " + path)
        add_source(sources, module, source, "supplement:" + path)
    return {"data": data, "source_modules": len(entries), "sha256": expected_digest}


def dependency_plan(sources: dict, roots: list[str]) -> dict:
    graph, externals, missing = {}, {}, {}
    pending = list(roots)
    while pending:
        module = pending.pop()
        if module in graph:
            continue
        if module not in sources:
            missing.setdefault(module, []).append("entrypoint")
            continue
        imports = source_imports(sources[module]["data"], module)
        rho5 = [dep for dep in imports if dep == "Rho5" or dep.startswith("Rho5.")]
        graph[module] = rho5
        for dep in imports:
            if dep not in rho5:
                externals.setdefault(dep, []).append(module)
        for dep in rho5:
            if dep not in sources:
                missing.setdefault(dep, []).append(module)
            elif dep not in graph:
                pending.append(dep)
    if missing:
        detail = json.dumps({k: sorted(set(v)) for k, v in sorted(missing.items())}, indent=2)
        raise AssemblyError("Missing recursive Rho5 imports:\n" + detail)
    indegree = {module: len(set(deps)) for module, deps in graph.items()}
    dependents: dict[str, list[str]] = {module: [] for module in graph}
    for module, deps in graph.items():
        for dep in set(deps):
            dependents[dep].append(module)
    ready = [module for module, degree in indegree.items() if degree == 0]
    heapq.heapify(ready)
    order = []
    while ready:
        module = heapq.heappop(ready)
        order.append(module)
        for dependent in sorted(dependents[module]):
            indegree[dependent] -= 1
            if indegree[dependent] == 0:
                heapq.heappush(ready, dependent)
    if len(order) != len(graph):
        raise AssemblyError("Recursive Rho5 import cycle among: " + ", ".join(
            sorted(module for module, degree in indegree.items() if degree)))
    return {
        "roots": roots,
        "dependency_first_order": order,
        "rho5_imports": dict(sorted(graph.items())),
        "external_imports_not_locally_verified": {k: sorted(set(v)) for k, v in sorted(externals.items())},
        "unknown_external_namespaces": sorted({k.split(".")[0] for k in externals}
                                               - KNOWN_EXTERNAL_NAMESPACES),
    }


def generated_lakefile(base_config: bytes, modules: list[str]) -> bytes:
    """Keep the frozen mathlib requirement, but avoid an absent Rho5 root."""
    text = base_config.decode("utf-8")
    marker = "[[require]]"
    if text.count(marker) != 1:
        raise AssemblyError("Unsupported frozen Lake configuration structure")
    requirements = text[text.index(marker):]
    module_globs = ",\n  ".join(json.dumps(module) for module in modules)
    generated = (
        '# Generated source-assembly recipe; NOT_LEAN_TESTED.\n'
        'name = "rho5Pilot"\nversion = "0.1.0"\n'
        'defaultTargets = ["PhaseTwoSnapshot"]\n\n'
        '[[lean_lib]]\nname = "Rho5"\nroots = ["Rho5.PhaseOne"]\n'
        f'globs = [\n  {module_globs}\n]\n\n'
        '[[lean_lib]]\nname = "PhaseTwoSnapshot"\nroots = ["PhaseTwoSnapshot"]\n'
        'globs = ["PhaseTwoSnapshot"]\n\n' + requirements
    )
    return generated.encode("utf-8")


def write_file(root: Path, path: str, data: bytes) -> None:
    destination = root.joinpath(*safe_relative(path).parts)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("xb") as handle:
        handle.write(data)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base", type=Path, required=True, help="Frozen public repo lean/ directory")
    parser.add_argument("--phase2-zip", type=Path, required=True, help="Published SHA-pinned B366 source-only ZIP")
    parser.add_argument("--supplement", type=Path, required=True, help="Dependency supplement root; source paths resolve here")
    parser.add_argument("--manifest", type=Path, required=True, help="Dependency manifest with sources[{module,path,sha256}]")
    parser.add_argument("--manifest-sha256", required=True, help="Expected dependency manifest SHA-256 from public release")
    parser.add_argument("--output", type=Path, help="NEW directory only; forbidden if it already exists")
    parser.add_argument("--verify-only", action="store_true", help="Check identities and static closure without writing")
    args = parser.parse_args()
    if not args.verify_only and args.output is None:
        parser.error("--output is required unless --verify-only is used")
    if args.output is not None and args.output.exists():
        parser.error("--output must not already exist")
    sources: dict = {}
    try:
        base = load_base(args.base, sources)
        snapshot, phase2 = load_phase2(args.phase2_zip, sources)
        supplement = load_supplement(args.supplement, args.manifest, args.manifest_sha256, sources)
        plan = dependency_plan(sources, snapshot)
        receipt = {
            "schema": "rho5-static-phase2-source-assembly-v1",
            "status": "STATIC_SOURCE_CLOSURE_PASS_NOT_COMPILATION",
            "scope": "Frozen source identities, comment/string-aware Rho5 import closure, and dependency order only.",
            "lean_executed": False, "network_used": False,
            "generated_lake_configuration": "GENERATED_NOT_LEAN_TESTED",
            "unconditional_paper_theorem_proved": False,
            "phaseone_manifest_sha256": BASE_MANIFEST_SHA256,
            "phaseone_manifest_files_checked": base["verified_manifest_files"],
            "phaseone_configuration_sha256": BASE_CONFIG_SHA256,
            "phase2_zip_sha256": PHASE2_ZIP_SHA256,
            "adopted_b366_modules": phase2["adopted_modules"],
            "compiled_support_modules_not_separately_adopted": phase2["support_modules"],
            "supplement_manifest_sha256": supplement["sha256"],
            "supplement_modules": supplement["source_modules"],
            "union_source_modules": len(sources),
            "recursive_snapshot_rho5_closure_modules": len(plan["dependency_first_order"]),
            "unknown_external_namespaces": plan["unknown_external_namespaces"],
            "sources": [{"module": module, "path": module_path(module),
                         "sha256": source["sha256"], "origins": source["origins"]}
                        for module, source in sorted(sources.items())],
        }
        if not args.verify_only:
            output = args.output
            output.mkdir(parents=True, exist_ok=False)
            for module, source in sorted(sources.items()):
                write_file(output, module_path(module), source["data"])
            for path, data in base["config"].items():
                destination = "lakefile.phaseone-frozen.toml" if path == "lakefile.toml" else path
                write_file(output, destination, data)
            # Keep base files untouched. This independent project has a new explicit target.
            write_file(output, "lakefile.toml", generated_lakefile(
                base["config"]["lakefile.toml"], plan["dependency_first_order"]))
            aggregate = ('/- Generated source-assembly entrypoint. NOT_LEAN_TESTED.\n'
                         '   Importing this snapshot does not discharge global safety assumptions. -/\n'
                         + "".join("import " + module + "\n" for module in snapshot))
            write_file(output, "PhaseTwoSnapshot.lean", aggregate.encode("utf-8"))
            for path, data in phase2["evidence"].items():
                write_file(output, "snapshot_evidence/" + path, data)
            write_file(output, "DEPENDENCY_MANIFEST.json", supplement["data"])
            write_file(output, "STATIC_ASSEMBLY_RECEIPT.json", (json.dumps(receipt, indent=2) + "\n").encode())
            write_file(output, "STATIC_BUILD_PLAN.json", (json.dumps(plan, indent=2) + "\n").encode())
            instructions = """# Frozen PhaseTwo source assembly

This directory combines the SHA-pinned public PhaseOne sources, the original
B366 snapshot (1,452 adopted plus four compiled reuse supports), and the pinned
dependency supplement. It does not modify any source input, fetch dependencies,
invoke Lean, or replace the PhaseOne cold-build record.

`STATIC_ASSEMBLY_RECEIPT.json` binds every output source to its input hash.
`STATIC_BUILD_PLAN.json` gives dependency-first Rho5 import order and records
external imports separately. This checks source availability, not declarations,
compiled objects, proof validity, axiom scope, or the large certificate trees.

The original Lake configuration is retained as `lakefile.phaseone-frozen.toml`.
The generated `lakefile.toml` uses the same pinned mathlib requirement and an
explicit `PhaseTwoSnapshot` target. It is GENERATED_NOT_LEAN_TESTED, including
the aggregate import entrypoint. Do not interpret a static pass as a build pass.

For a later, separately authorized compiler check, with the exact Lean toolchain
and the locked dependencies installed, the intended explicit command is:

```sh
lake build PhaseTwoSnapshot
```

No successful result from that command is supplied by this assembly helper.
Record any actual compiler exit code, source identities, toolchain, build logs,
and theorem axiom audits separately. `XGlobalSafety` and `RootEndpointSafety`
remain explicit global assumptions; this assembly does not prove the paper's
unconditional rho5 equality or bring the external exact trees inside Lean.
"""
            write_file(output, "README_SOURCE_ASSEMBLY.md", instructions.encode())
        print(json.dumps({key: value for key, value in receipt.items() if key != "sources"}, indent=2))
        return 0
    except (AssemblyError, OSError, ValueError, KeyError, zipfile.BadZipFile) as e:
        print("ASSEMBLY_FAILED: " + str(e), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
