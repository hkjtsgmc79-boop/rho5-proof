# Bounded audit of D162 cold-rebuild evidence

Audit date: 2026-09-12. Read-only inspection of the local Lean delivery; no builds, remote work, or Lean-project changes.

Source evidence root: `/Users/mike/Documents/Codex/2026-09-11/rho5-lean-formalization/outputs/d162_phase1_cold_rebuild_20260912/`.

Frozen source root: `/Users/mike/Documents/Codex/2026-09-11/rho5-lean-formalization/outputs/phase1_noncomputational_assembly_20260912/P01/`.

## Finding

The recorded project cold rebuild completed on 12 September 2026 at 21:58:48 UTC+08:00. The acceptance scope was the 634-module frozen product import closure, three additional example/audit modules, 47 named axiom checks, and explicit checking of the two remaining safety parameters. The actual final type is `XGlobalSafety → RootEndpointSafety → rho5Trace = alpha`. This does not establish the two safety propositions or provide an unconditional Lean proof of the sharp equality. Second-phase tree/certificate work remained frozen.

The project began from zero Rho5 objects after discarding 19 objects from an invalid preliminary run (`FINAL_DELIVERY/evidence/clean_cold_start.txt`); later lanes consumed only newly compiled objects from this same run. Fixed third-party dependency caches were reused, with missing Mathlib ODE dependencies subsequently compiled. `PRODUCT_634_COMPLETE_2155.json` records `closure2_done.json` with 291 modules built and `Mathlib.Analysis.ODE.PicardLindelof` ready. This is a project cold rebuild, not a fresh-machine rebuild of Lean and all dependencies.

The documented command `lake build +Rho5.PhaseOne:olean` failed because `Conditional.olean` was absent. A Lake discovery configuration revision was not accepted as a completed build. The accepted route used explicit dependency ordering and per-module Lean invocations, eventually across the authorized six lanes. Do not describe the complete run as globally serial merely because the final summary says “single Lean”; that limit applied per lane after the later authorization.

## Independently checked locally

- All 38 entries of `FINAL_DELIVERY/SHA256SUMS` match the actual local files (405,109 bytes total).
- The actual `D162_COLD_REBUILD_RECEIPTS_20260912.tgz` hash is `c0ec1be2dc8b2aff26f987d13be34a20f0f2e92a4d2389523e9fe88c9c980415` (107,995 bytes).
- The actual frozen `P01/SOURCE.zip` hash is `ddb1e4300ed03464024f2a2a227cee060b6b38de96a02043f9233f0412e28f56` (6,428,728 bytes).
- `SOURCE_AND_OBJECT_MANIFEST.json` contains exactly 634 distinct module records, all with positive object size. Three bounded source samples (Horner, Conditional, PhaseOne) match their recorded source hashes.
- `lean_extras2_Audit.stdout` contains 33 parsed axiom declarations; `lean_extras2_ExamplesAudit.stdout` contains 14. Independent parsing, including multiline lists and normalization of universe suffixes, matches all 47 named frozen `P01/project/AXIOMS.json` records exactly. The union is `{propext, Classical.choice, Quot.sound}`; no targets are missing and no extra axioms appear in these 47 checks.
- `lean_finalize3_HxB_check.stdout` actually prints the conditional theorem and both safety propositions. `P01/project/Rho5/Integration/StagedAssembly/Conditional.lean:20` retains explicit `hX` and `hB` parameters.
- The local frozen lock/config hashes match the environment receipt: `lake-manifest.json` SHA256 `6fa600a652ca1ef77814e08127d1078febb38e3018ed9f8b1c5683b92427b789`; `lakefile.toml` SHA256 `bb06bd656723ce3c57074d9bf2c028540baaf87e43469cb186ac16ce4d35a358`.

The toolchain receipt records Lean 4.30.0, Linux x86_64, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, and Mathlib revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Evidence limitations

The local receipt archive contains the object/source manifest, final build and gate receipts, finalizer logs, actual axiom/type output, and failed-build evidence. It does not contain the 634 full per-module compilation logs, all Linux objects, or reproduction drivers. The 634-module compilation acceptance is supported by the owner's full gate log (`verified_634=634 bad=0`), the manifest, and the coordinator's deduplicated receipts; this audit did not revalidate remote objects or rerun Lean. The delivery cannot by itself be described as a standalone end-to-end replay archive.

## Suggested manuscript replacement

“The frozen first-phase Lean sources were rebuilt on Linux on 12 September 2026 from an empty project-object directory, using Lean 4.30.0 and pinned third-party dependencies. The recorded rebuild passed all 634 product modules, three additional example/audit modules, and 47 named axiom checks. It used an explicit dependency-order build driver; the original packaged Lake command did not pass in the cold state. Third-party caches were reused and supplemented where needed. The final Lean equality remains conditional on `XGlobalSafety` and `RootEndpointSafety`; the large tree and certificate stage was not replayed.”

For a shorter replacement of only the original negative claim:

“A cold rebuild of the frozen first-phase Lean project has now completed on Linux, with pinned third-party dependency caches reused and supplemented as needed. This verifies the conditional first-phase development through an explicit dependency-order driver; it does not constitute a fresh-machine dependency build or a new end-to-end replay of the tree and certificate stage.”
