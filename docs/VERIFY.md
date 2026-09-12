# Verify the RHO5 materials, step by step

This guide separates **Lean proof checking**, **exact certificate checking**, and **file-identity checking**. A successful step is credited only for its stated scope. The release preserves recorded computations; publishing it is not a new complete mathematical replay.

## 1. Obtain the fixed source version

```sh
git clone --branch v1.0.0 --depth 1 https://github.com/hkjtsgmc79-boop/rho5-proof.git
cd rho5-proof
git rev-parse HEAD
python3 scripts/fetch.py --list
```

Keep the printed commit hash with your verification records. The repository contains source and instructions; the large certificates are separate release assets. [DOWNLOADS.md](DOWNLOADS.md) gives exact sizes and resource allowances.

The helper uses only Python's standard library. Downloads are selected explicitly; it checks SHA-256 and rejoins transport parts. Rerunning the same command resumes partial downloads. Download success is not a mathematical result.

## 2. Check the Lean analytic development

Install elan using its official installation instructions if it is not already available. From the checkout:

```sh
cd lean
elan toolchain install leanprover/lean4:v4.30.0
lake --version
lake exe cache get
lake build +Rho5.PhaseOne:olean
lake build +Rho5.PhaseOne.Audit:olean
lake build +Rho5.PhaseOne.Examples:olean
lake build +Rho5.PhaseOne.ExamplesAudit:olean
```

The fixed mathlib revision is `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Preserve the committed lock file; do not upgrade dependencies as a workaround for a failed build. `cache get` obtains third-party precompiled dependencies, not a substitute for checking the project source.

The default product is `Rho5.PhaseOne`. It includes 634 loaded project modules out of 646 canonical source files. It does not select the deferred full-tree Lean experiments.

Expected result: successful module builds and the declared theorem/axiom output. Inspect [the full public types](../lean/FINAL_THEOREM_TYPES.txt) and [recorded axioms](../lean/AXIOMS.json). The sharp endpoint has two visible assumptions:

```lean
Rho5.PhaseOne.rho5Trace_eq_alpha_of_safety
  (hX : Rho5.Integration.StagedAssembly.XGlobalSafety)
  (hB : Rho5.Shared.BRootCapacityEndpoint.RootEndpointSafety) :
  Rho5.GrowthSupremum.rho5Trace = Rho5.Algebraic.AlphaRoot.alpha
```

Successful compilation does not remove those hypotheses. Their full global discharge, including the remaining model and coverage connections, is not supplied as a Lean proof in this first-phase release.

The recorded new-entry/audit/example builds reused accepted X caches. A fresh-machine cold build of the entire published source closure was not performed during publication. See [the original build notes](../lean/docs/BUILDING.md) for provenance and limitations.

## 3. A small real certificate

Return to the repository root. Use Python 3.10 or newer without `-O` and without `PYTHONOPTIMIZE`.

```sh
python3 scripts/fetch.py --group sample
python3 -m zipfile -e downloads/rho5-final-anchor-example.zip replay-output/anchor
cd replay-output/anchor
python3 -S restore_inputs.py
python3 -S verify_joint_anchor.py \
  --v53-dir rho5_v53_exact \
  --b16-dir B_STRUCTURE_16_DELIVERY \
  --output-dir replayed_anchor
```

Use a new extraction directory. The output `replayed_anchor` must not already contain a previous completed run. This example uses the standard library; it does not require an optimizer or GPU.

The key expected fields are:

```text
COMPLETE_ANCHOR_ALPHA_SAFE
parent_index = 435003
anchor_path = 10011101
paid_leaves = 54
remaining_sources = []
whole_parent_closed = false
whole_B_closed = false
```

The two `false` values are intentional. This certificate proves the complete named anchor safe at alpha; other certificates are required for the full parent and B domain. The historical exact run took approximately 184.37 seconds on X. That is neither a whole-proof timing nor a timing guarantee for your machine.

## 4. Check the X-domain components

From the repository root:

```sh
python3 scripts/fetch.py --group x --group upstream
```

Extract each archive into its own directory. The following are existing verifier entry points, run from their package roots. Keep the archived directory structure, model and frozen verifier together.

| Component | Archive | Entry from the extracted package |
|---|---|---|
| Small k | `rho5_v31_exact.zip` | `python3 verify_all.py` |
| Large k | `ROUND43_MINIMAL_REPLAY.zip` | In `RHO5_CQG_ROUND43`: `bash repro/replay.sh` |
| Midband | `ROUND44_MINIMAL_REPLAY.zip` | In `ROUND44_MINIMAL_REPLAY`: `python3 repro/replay_new.py .` |
| V33 slice | `rho5_v33_exact.zip` | In `rho5_v33_exact`: `python3 verify_all.py` |
| Round45 | `RHO5_ROUND45_EXACT.zip` | In `rho5_round45_exact`: `python3 replay.py` |
| Strict high r | `RHO5_V34_HIGH_EXACT_FULL.zip` | In `rho5_v34_high`: `python3 replay_high.py` |
| Low r / alpha | `RHO5_ROUND47_ALPHA_FULL.zip` | In `rho5_round47_alpha`: `python3 replay.py` |

Read each archive's README for supported switches. These components generally require Python/SymPy, a C++17 compiler and Boost.Multiprecision headers. Round43 supports `RHO5_PYTHON` and `BOOST_INCLUDE`; Round44 supports `--boost-include`. Do not assume that one environment override applies to every historical package. The V31 archive has a documented GCC9 naming-compatibility issue in its historical review; use its recorded compatibility handling rather than silently changing mathematical rules.

The accompanying upstream assets preserve V24/T24 canonical reduction, V25 reconstruction nested within V26, V27 entrance information, V28 canonical height, and the V36/V37 assembly/reduction packages. A local component PASS does not alone supply all upstream analytic and domain coverage arguments. Follow the [supplementary index](../paper/RHO5_SUPPLEMENTARY_INDEX.pdf), S3–S5, and the original dependency manifests.

The `verifiers/` directory is an online-readable source mirror, indexed by [verifier-source-map.json](../manifests/verifier-source-map.json). Run the original complete archive, not a stripped source mirror missing its data. Different packages may intentionally contain different versions of the same verifier filename.

## 5. Check the B root and final covers

```sh
python3 scripts/fetch.py --group b
```

The helper reassembles `historical_root.tar.gz` from five transport parts and checks the original archive hash. Retain enough disk for the parts, reconstructed archives, approximately 21.54 GB of outer extracted B files, and additional runtime expansion/output.

Extract `historical_root.tar.gz` and `final_cover.tar.gz` into a separate Linux working directory, preserving their internal paths. From `rho5_independent_acceptance_20260911_11`, the existing base-root entry is:

```sh
python3 -B -S runtime/r54_replay.py \
  --tree checkpoint/B17_ROOT.json \
  --out REPLAY_ROOT_NEW.json \
  --workers 8 --backend fraction --allow-open
```

Use a new output filename. The expected original-root result is `PARTIAL_EXACT_COVERAGE_ONLY`: 749,693 nodes, 374,839 contradiction terminals, 4 alpha-safe terminals and 4 open terminals. The four original open terminals are paid by the separate final covers. `--allow-open` does not license an incomplete final proof.

The complete B route then replays the four parent contributions, the alpha-cover mathematics and the final 54-leaf anchor before composing the source-bound covers. The archive contains the relevant code and records, including `deep_math.verify_branch`, `alpha_cover.verify_cut` and `final_overlay_accept.py`.

**Portability boundary:** there is not yet one tested, location-independent command that replays this entire chain from scratch. Some composition configurations contain original absolute paths, and the final composer consumes previously checked receipts. Fresh reproduction must prepare an explicit path mapping, preserve frozen source hashes and the 435003 parent’s frozen 239/240 baseline, rerun all necessary mathematical dependencies, and compose the newly generated records. Do not disable source checks or replace this work with receipt-hash checking. See S7–S8 of the supplement for the precise composition scope.

## 6. Read the combined conclusion

The proof combines the written analytic arguments with complete component verification and exact source/domain coverage. It includes the actual alpha constant and an attaining matrix; it quantifies over real matrices and all legal pivot choices. The Lean theorem map is provided separately and keeps its remaining global hypotheses visible.

For your own reproduction, record the source commit, manifest hash, environment, exact commands, wall time, worker count, peak RAM/disk if measured, exit status, and mathematical scope. Distinguish:

1. Files downloaded and hash-checked.
2. Lean declarations checked with their full hypotheses.
3. Individual exact certificates checked.
4. All necessary sources and domains composed.

The original acceptance records are evidence of those recorded runs; they are not a new run on your computer.

## Troubleshooting

- **Interrupted download:** rerun the same fetch command. A partial `.download` is resumed when the server supports ranges; a server returning a full file restarts that download safely.
- **Wrong existing archive:** the helper refuses to overwrite it silently. Move the conflicting file aside and fetch the fixed asset again.
- **Old output directory:** create a new output location. Frozen verifiers may deliberately reject overwriting accepted receipts.
- **Lean dependency mismatch:** check `lean-toolchain` and `lake-manifest.json`; retain the pinned versions.
- **Missing certificate input:** obtain the original archive and referenced dependency assets. The source mirror alone is not a runnable certificate bundle.
- **Open fields in an intermediate receipt:** check its stated scope. Full coverage is a composition claim, not the demand that every preserved historical file have zero open fields.

For questions, report the release, exact command and relevant error without changing the frozen mathematical inputs.
