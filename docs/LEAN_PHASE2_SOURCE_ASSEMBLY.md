# Second-phase Lean source assembly

The B366 source snapshot and its dependency supplement are **source review materials**. The supplied assembly helper has been run and its output hashes checked. No combined second-phase Lean build or whole-tree verification is claimed.

## Inputs and identities

- The [frozen first-phase base](../lean/) retains the source/configuration identities in the original `v1.0.2` commit `007ac53dbd6194b56b6fc2d120b3ab1e294aa64a`. The current main branch adds publication material without changing those base files.
- The original [B366 source ZIP](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2/RHO5_Lean_Phase2_B366_SOURCE_ONLY_v1.0.2.zip) has SHA-256 `3c4dcb433ad5af1deee9c2f18531e862110c62c501cdbe5c54ed2a9d06d97fc7`.
- The [dependency supplement ZIP](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2-lean-deps.1/RHO5_Lean_Phase2_B366_DEPENDENCY_SUPPLEMENT_v1.0.2.zip) has SHA-256 `feef442da639bb9ddffc26136c9393223d6a888e8eadd7c788de9ab82d9594f0`. Its source files, historical evidence and helper are also browsable under [lean-phase2-support/](../lean-phase2-support/).

The fixed original tag and five original attachments remain unchanged. The separate `v1.0.2-lean-deps.1` dependency release and current main-branch index were added on 30 September 2026. GitHub locks the original release assets, so this source supplement uses a separate tag; it does not change the paper version. Thus the fixed tag's original download script does not know about the new attachment; use current main or the direct URLs.

## Actually tested static route

From a current main-branch checkout, download only the B366 snapshot and supplement:

```sh
python3 scripts/fetch.py --id phase2_source --id phase2_dependencies
python3 lean-phase2-support/assemble_phase2.py \
  --base lean \
  --phase2-zip downloads/RHO5_Lean_Phase2_B366_SOURCE_ONLY_v1.0.2.zip \
  --supplement lean-phase2-support \
  --manifest lean-phase2-support/DEPENDENCY_MANIFEST.json \
  --manifest-sha256 00348c9d0508a364e3b6ffed51957a896592891ef25d0677c77095cb31d54a67 \
  --output ../rho5-phase2-source-assembly
```

Use a new output directory. Python 3.10+ and the standard library suffice. `--verify-only` performs the same identity and static import checks without writing an assembled project. The helper does not fetch dependencies, launch Lean or execute certificates.

Expected result: `STATIC_SOURCE_CLOSURE_PASS_NOT_COMPILATION`, with 1,452 adopted B366 modules, four identified supports, 76 supplied dependencies, and 2,027 reachable Rho5 source modules. The output contains 2,178 source modules including base modules outside that reachable snapshot closure. Source files are checked against their pinned identities; conflicting versions, missing Rho5 imports, cycles and unsupported import syntax are rejected.

The [static receipt](../lean-phase2-support/STATIC_ASSEMBLY_RECEIPT.json), [dependency plan](../lean-phase2-support/STATIC_BUILD_PLAN.json), [source provenance check](../lean-phase2-support/SOURCE_PROVENANCE_CHECK.json) and [helper checks](../lean-phase2-support/ASSEMBLY_HELPER_CHECKS.json) record these bounded checks. Every supplied source has a matching historical source-bound successful compilation or owner acceptance record. Those original records retain their original hypotheses and scope; the CertificateRules records include a scope correction. They do not certify a new joint build.

## Intended compiler route and its limits

The generated project preserves Lean `leanprover/lean4:v4.30.0`, mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f` and the original third-party lock file bytes. The old base configuration is saved as `lakefile.phaseone-frozen.toml`. Toolchains, third-party source/cache downloads and compiled project objects are separate inputs.

The generated `lakefile.toml` and aggregate `PhaseTwoSnapshot.lean` target are marked `GENERATED_NOT_LEAN_TESTED`. With the locked dependency environment installed, the intended command is:

```sh
lake build PhaseTwoSnapshot
```

This is an untested compiler target, not a recorded successful combined build. Preserve the lock and record actual fetched revisions, compiler errors and the exact source identity before treating a subsequent run as new acceptance. The [first-phase cold-build record](LEAN_COLD_REBUILD.md) remains a distinct historical result.

This source supplement neither executes the large certificate trees nor proves a whole-tree `check=true`, and it does not remove `XGlobalSafety` or `RootEndpointSafety`. The paper's written analytic proof and external exact certificates remain the mathematical claim; the unconditional full-paper Lean theorem is outside the published formalization scope. See the [proof map](PROOF_MAP.md) and [verification guide](VERIFY.md).
