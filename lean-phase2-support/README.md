# RHO5 B366 source dependency supplement

Prepared on 30 September 2026 as an additive supplement to the fixed GitHub v1.0.2 tag. The original article, index, five release attachments and tag are unchanged.

## Contents and verified scope

The original B366 ZIP retains all 1,452 adopted sources (151,211 physical lines), plus four separately identified reuse supports. That ZIP alone omits 57 directly imported Rho5 dependencies. The frozen first-phase source provides 39 of them; this supplement provides the other 18 and their missing recursive source dependencies: **76 additional source modules** in total.

Every supplied source matches a historical successful source-bound compiler or owner acceptance record. These records are supplied under `historical_evidence/`; they describe their original runs and hypotheses. They are not a new compilation of the combined project. In particular, the retained CertificateRules records must be read with their supplied scope correction.

With the frozen public first-phase sources, B366 ZIP and this supplement, the static recursive source closure contains **2,027 Rho5 modules**. The assembly helper checks fixed hashes, rejects conflicting source versions, missing imports and cycles, and writes a dependency-first plan. Third-party Lean/mathlib imports are recorded separately. Source-import completeness is not a proof of compatible elaboration or of a mathematical result.

## Obtain the three inputs

1. The frozen base checkout: `git clone --branch v1.0.2 --depth 1 https://github.com/hkjtsgmc79-boop/rho5-proof.git`. Its commit is `007ac53dbd6194b56b6fc2d120b3ab1e294aa64a`.
2. [Original B366 source snapshot](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2/RHO5_Lean_Phase2_B366_SOURCE_ONLY_v1.0.2.zip), SHA-256 `3c4dcb433ad5af1deee9c2f18531e862110c62c501cdbe5c54ed2a9d06d97fc7`.
3. This dependency supplement. Extract it into a new directory beside the base checkout and B366 ZIP.

The original tag predates this additive supplement. Its original downloader therefore does not list the new attachment. The current GitHub main branch has a unified download index; the fixed direct release URLs above remain usable with the original tag.

## Static assembly — actually tested

From the extracted supplement directory, with the sibling paths described above:

```sh
python3 assemble_phase2.py \
  --base ../rho5-proof/lean \
  --phase2-zip ../RHO5_Lean_Phase2_B366_SOURCE_ONLY_v1.0.2.zip \
  --supplement . \
  --manifest DEPENDENCY_MANIFEST.json \
  --manifest-sha256 00348c9d0508a364e3b6ffed51957a896592891ef25d0677c77095cb31d54a67 \
  --output ../rho5-phase2-source-assembly
```

Use a new output directory; an existing directory is rejected. `--verify-only` instead performs the identity/closure checks without writing a project. Expected static status: `STATIC_SOURCE_CLOSURE_PASS_NOT_COMPILATION`, with 1,452 adopted sources, four supports, 76 supplied dependencies and 2,027 reachable Rho5 modules. The original base configuration is retained under `lakefile.phaseone-frozen.toml`.

## Compiler route — not yet tested as a combined project

The generated project retains Lean `leanprover/lean4:v4.30.0`, mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f` and the original third-party lock bytes. Lean/toolchains/dependency caches and compiled project objects are not included. Preserve the lock and record the actual fetched revisions; do not upgrade dependencies to bypass a failed build.

The generated `lakefile.toml` and `PhaseTwoSnapshot.lean` are explicitly `GENERATED_NOT_LEAN_TESTED`. With the locked dependency environment present, the intended explicit compiler target is `lake build PhaseTwoSnapshot`. No successful combined build or new axiom audit for that target is supplied. The original first-phase cold-build record remains a separate historical result.

This supplement does not run the large certificate trees, prove a whole-tree `check=true`, or remove `XGlobalSafety` and `RootEndpointSafety`. The unconditional full-paper Lean theorem remains outside the claimed scope. The paper's written analysis plus external exact certificates are unchanged.
