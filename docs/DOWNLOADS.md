# Downloads, disk space and computing time

**Current documents: v1.0.2. Frozen original certificate inventory: v1.0.0.** The newer release links the original assets; it does not duplicate or change them. The [v1.0.2 release index](../manifests/v1.0.2.json) records the revised paper and new dated evidence; the [original certificate manifest](../manifests/release-assets.json) retains its fixed URLs and hashes. MB and GB below are decimal; GiB is binary.

The [88-page article and 9-page index](https://doi.org/10.5281/zenodo.23057256) are archived at Zenodo with their own version DOI. GitHub v1.0.2 also supplies source and verification material, including the 30 September negative-diagonal replay records and a **source-only** second-phase Lean review snapshot. The [dated replay guide](REPLAY_20260930.md) explains which parts are executable mathematics and which are file or receipt checks.

## New v1.0.2 attachments

These six objects total **6,226,081 bytes**. The dependency supplement was added on 30 September after the original five attachments; the fixed tag and original file hashes are unchanged. Their exact sizes and SHA-256 values are in [the v1.0.2 release index](../manifests/v1.0.2.json). The two PDFs are byte-identical to the published Zenodo version; the ZIPs are additional GitHub materials.

| Attachment | Bytes | Contents |
|---|---:|---|
| [Article PDF](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2/rho5_manuscript_v1.0.2.pdf) | 477,462 | Published 88-page manuscript |
| [Supplementary index PDF](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2/RHO5_SUPPLEMENTARY_INDEX_v1.0.2.pdf) | 91,402 | Published 9-page index |
| [Source and bounded checks](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2/RHO5_v1.0.2_source_and_checks.zip) | 126,083 | Matching TeX/Bib source, changes, responsibility map and small exact checks |
| [Dated replay evidence](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2/RHO5_v1.0.2_replay_evidence.zip) | 2,962,411 | Executed plan and drivers, final receipt export, source mapping and separate audits |
| [Partial Lean source snapshot](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2/RHO5_Lean_Phase2_B366_SOURCE_ONLY_v1.0.2.zip) | 2,048,268 | B366 second-phase source review; no standalone cold build or unconditional theorem |
| [Lean dependency supplement](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2/RHO5_Lean_Phase2_B366_DEPENDENCY_SUPPLEMENT_v1.0.2.zip) | 520,455 | 76 historical source versions, acceptance evidence and tested static assembly helper; no new combined Lean build |

The dated replay ZIP does not include the inherited 3.575 GB compressed B archives or all mathematical runtime inputs. Its `verify_public_replay_bundle.py` checks the supplied receipt identities and 570 links, not the underlying mathematics. The clean-directory assembly of its source layout from public archives is a separately recorded portability gate; see [the replay guide](REPLAY_20260930.md).

## Choose what to download

Use `python3 scripts/fetch.py --list` to list object ids. On the current main branch, choose `--group sample`, `--group lean`, `--group x`, `--group b`, `--group upstream`, `--group analytic`, `--group paper`, or `--group replay`. `--all` selects the inherited inventory and all six v1.0.2 attachments. The frozen v1.0.2 tag predates the added supplement and retains its original downloader; use current main or the fixed direct URLs for the new attachment. The helper checks every downloaded file and reconstructs multipart archives.

| Group | Logical archive | Download | Outer extracted payload |
|---|---|---:|---:|
| lean | [rho5-lean-phase-one.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/rho5-lean-phase-one.zip) | 6.43 MB | 40.62 MB |
| sample | [rho5-final-anchor-example.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/rho5-final-anchor-example.zip) | 18.29 MB | 41.65 MB |
| x | [rho5_v31_exact.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/rho5_v31_exact.zip) | 15.80 MB | 15.95 MB |
| x | [ROUND43_MINIMAL_REPLAY.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/ROUND43_MINIMAL_REPLAY.zip) | 12.19 MB | 36.81 MB |
| x | [ROUND44_MINIMAL_REPLAY.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/ROUND44_MINIMAL_REPLAY.zip) | 79.49 MB | 250.76 MB |
| x | [rho5_v33_exact.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/rho5_v33_exact.zip) | 51.80 MB | 53.16 MB |
| x | [RHO5_ROUND45_EXACT.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/RHO5_ROUND45_EXACT.zip) | 222.15 MB | 222.60 MB |
| x | [RHO5_V34_HIGH_EXACT_FULL.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/RHO5_V34_HIGH_EXACT_FULL.zip) | 131.84 MB | 133.46 MB |
| x | [RHO5_ROUND47_ALPHA_FULL.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/RHO5_ROUND47_ALPHA_FULL.zip) | 367.18 MB | 371.03 MB |
| b | [final_cover.tar.gz](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/final_cover.tar.gz) | 1.385 GB | 3.704 GB |
| b | [historical_root.tar.gz](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/tag/v1.0.0) (5 transport parts) | 2.190 GB | 17.836 GB |
| upstream | [RHO5_V24_Exact_Verification_2026-09-06.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/RHO5_V24_Exact_Verification_2026-09-06.zip) | 7.76 MB | 16.17 MB |
| upstream | [RHO5_V26_Canonical_Global_Alpha_Exact_Verification_2026-09-07.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/RHO5_V26_Canonical_Global_Alpha_Exact_Verification_2026-09-07.zip) | 0.07 MB | 0.09 MB |
| upstream | [rho5_v27_verify.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/rho5_v27_verify.zip) | 0.04 MB | 0.09 MB |
| upstream | [rho5_v28_exact.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/rho5_v28_exact.zip) | 3.75 MB | 4.26 MB |
| upstream | [rho5_v36_exact.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/rho5_v36_exact.zip) | 0.83 MB | 5.03 MB |
| upstream | [rho5_v37_exact.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/rho5_v37_exact.zip) | 0.90 MB | 1.99 MB |
| analytic | [RHO5_PAPER_REVIEW_PHASE1_20260912.zip](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/RHO5_PAPER_REVIEW_PHASE1_20260912.zip) | 0.86 MB | 4.30 MB |

The inherited original archive inventory totals **4,494,382,372 bytes (4.494 GB)**. It contains intentional overlap (for example, the small final-anchor example and corresponding B material). The v1.0.2 document and evidence attachments are additional. Do not interpret a sum of package sizes as a proof of transitive dependency closure.

`RHO5_PAPER_REVIEW_PHASE1_20260912.zip` preserves the original pre-GitHub review collection byte for byte, including its historical publication-status fields. The current paper with the public repository address is in [paper/](../paper/); the old review record is not a statement about the present availability of this release.

Outer extracted sizes sum regular archive-member sizes. They exclude nested compressed-tree expansion, third-party packages, build caches, filesystem overhead and new verification outputs. The two B archives alone contain approximately **21.54 GB** of outer regular-file payload. Retained hard links may reduce actual disk use.

The historical-root archive exceeds GitHub’s per-asset limit. Five byte-transport parts reproduce the original 2,189,588,699-byte archive exactly. Keep room for both parts and the reconstructed archive until you choose to remove transport copies. The mathematical tree has not been changed.

## Lean size and observed timings

- Canonical project source: **646 modules, 35,027,225 bytes**. The default product loads 634 project modules.
- Original source ZIP: **6,428,728 bytes**, expanding to **40,620,705 bytes** including docs and evidence; 2 additional `.lean` members are evidence copies, not new canonical modules.
- The separate B366 second-phase archive preserves 1,452 adopted source modules (151,211 physical lines) and four identified support sources. Of 57 direct Rho5 imports outside that snapshot, 39 are in the frozen first-phase base; the dependency supplement adds the other 18 and missing recursive dependencies, 76 sources in total. Static assembly confirms a reachable closure of 2,027 Rho5 modules. This is source availability, not a new combined compilation or Lean acceptance of the full theorem. See the [assembly guide](LEAN_PHASE2_SOURCE_ASSEMBLY.md).
- Lean 4.30.0 and pinned mathlib are separate downloads. Their caches and compiled project objects are not included in the source ZIP.

| Recorded check | Wall time | Scope and environment |
|---|---:|---|
| PhaseOne entry and audit | 8.051 seconds | X, reusing accepted upstream caches |
| Frozen project cold-rebuild session | About 4 hours 11 minutes | Linux, 634 + 3 modules and 47 checks; includes recovery and dependency work, not a clean benchmark |
| Examples and example audit | 12.021 seconds | Separate cached X run |
| Final 54-leaf anchor | 184.37 seconds | Historical exact X run of the named anchor |
| Original B root | 22,815.35 seconds (6.34 hours) | Historical X run, 8 processes, Fraction backend |
| 30 September fresh B root | 12,965.7057178 seconds (about 3 h 36 min) | Existing X host, 16 Fraction workers; original root only, excluding 570 producer calls and final composition |

The entry/audit and example timings are cached runs. The cold-rebuild row records a separate completed session; fixed third-party caches were reused and supplemented. See [the build scope](LEAN_COLD_REBUILD.md). Both root rows exclude parent/alpha-cover checks and source composition. These wall times are not summed CPU seconds or total discovery cost. No whole-proof runtime is inferred from them.

## Provisional resource allowances

These are practical planning allowances, **not measured minimum requirements or runtime guarantees**. Peak resources for a complete clean reproduction remain to be measured.

| Route | Planning allowance | Timing guidance |
|---|---|---|
| Small exact anchor | Standard CPU machine, Python 3.10+, about 1 GB free working disk | About 3 minutes in the historical X run; other machines vary |
| Lean first-phase build | Prefer Linux x86-64 for the first documented reproduction; reserve 32 GB RAM and 30–50 GB disk for toolchain/caches/output; start with low concurrency | Project cold session recorded at about 4 h 11 min; full dependency-from-scratch time remains unmeasured. Read the known command limitation before attempting a cold build |
| Full exact computational collection | Plan for an 8-process CPU machine, 32 GB RAM and **at least 50 GB free working disk** for data and output; allow more if retaining all transport copies | Base-root component alone took 6.34 hours; schedule a day or longer for the whole chain, not as a proven upper bound |
| Keeping Lean and all exact materials together | **80–100 GB free disk** is a provisional allowance for downloads, extracted data, toolchains/caches and working output | Final measured peak usage remains open |

No GPU is needed by the documented exact verifier entries. No new proof search is required. Worker limits differ between frozen verifiers; use each tool’s supported options. Do not enable Python assertion optimization (`-O` or `PYTHONOPTIMIZE`).

## Records to keep

For each independent run record the release/commit, asset manifest hash, processor model, software versions, workers, wall time, actual CPU time if measured, peak RAM/disk, commands and scoped mathematical results. See [VERIFY.md](VERIFY.md) for intermediate open fields and [PROOF_MAP.md](PROOF_MAP.md) for the distinction between Lean, exact acceptors and final coverage.
