# RHO5 verification protocol — v1.0.2 revision

Updated 30 September 2026. This protocol documents existing proof objects, frozen interfaces and their required dependency order. The new negative-diagonal finite-cover replay completed at 15:25:49 Beijing time in an isolated directory on the existing X host: all 570 parent producers and the fresh original-root run passed, and their source-bound composition has `effective_open_count = 0`. This result is conditional on the retained upstream analytic and complete-X arguments; their entire dependency chain was not rerun. Consult the accompanying status and final acceptance record for the run evidence. No new-machine whole-theorem replay, independent acceptor implementation or Lean rebuild was performed. A protocol is not an acceptance record.

## Scope and dependency order

The complete computer-assisted argument uses the written analytic proof, finite exact certificates, and complete source/domain composition. Its minimal mathematical direction is:

> Constant and attainment; early pivots and saturation → canonical representative/reconstruction/height → complete X bound → negative-diagonal source/rules and complete cover → sharp global equality.

This does not require replaying every abandoned search or every historical version. It does require every mathematical dependency actually consumed by the retained proof, recursively. An asset inventory or a list of direct dependencies is not evidence that this recursion is complete.

| Stage | Mathematical responsibility | Input/entry | Acceptance requirement |
|---|---|---|---|
| 1 | Constant and attaining matrix | Supplement S1; `supplement/foundations/work/verify_p5_exact.py`, `candidate_interval_newton.py`, `candidate_primal_cp_certificate.py`, with their preserved `work/` and `outputs/` structure | Exact polynomial identity/root isolation, denominator qualifications, reconstruction and a legal attaining CP path |
| 2 | Early pivots, exact lift, saturation, zero/tie cases | Written Sections 2–5 and S2 | Universal analytic argument; finite regressions do not replace it |
| 3a | Canonical representative exclusions and nested predecessors | `RHO5_V24_Exact_Verification_2026-09-06.zip`, root `RHO5_V24/`: `python3 verify.py --jobs 4 --full-chain` | All 22 invoked V20/V22/V24 trees; no unresolved leaf; invoked algebra/reconstruction checks |
| 3b | Row-scale reconstruction and canonical height | V25 nested in V26; `rho5_v28_exact.zip`, root `rho5_v28_exact/`: `python3 verify_v28_all.py` | All required modules, 13 localization grafts, 3 peak-box containments and their height module; analytic hypotheses remain part of the proof |
| 4 | Complete X bound | All seven entries below; S4 assembly | All named roots complete for their precise domains, with qualified local exits and upstream height theorem |
| 5 | Negative-diagonal source and acceptance semantics | V36/V37 source reductions, `B17_FULL.json`, S5–S6, actual frozen runtime dependencies | Complete physical source inclusion; every rule's qualification and actual-source binding |
| 6 | Original negative-diagonal root | `historical_root.tar.gz`: `rho5_independent_acceptance_20260911_11/runtime/r54_replay.py` | The specific partial cover below, including exactly four retained root O records |
| 7 | Four residual parents | `final_cover.tar.gz`; exact branch/cut interfaces below; final 54-terminal anchor | Complete frozen target sets, including inherited closed complements; 111/111, 240/240, 159/159, 56/56 |
| 8 | Source composition and global theorem | Parent composer, final root overlay, mixed-threshold cover theorem | All four actual root paths/boxes bound; effective OPEN zero; no confusion between gamma contradiction and alpha safety |

Stage 3 must precede the high-level use of Stage 4. The complete X bound then supports qualified negative-diagonal transport at Stages 5–7. The negative-diagonal conclusion is not an upstream premise of canonical height.

## Public version identities and files

The current source checkout is v1.0.2. It indexes unchanged certificate assets originally published under v1.0.0. Keep the fixed asset URLs and SHA-256 identities rather than relabeling old certificate bytes as newly generated mathematics. The v1.0.2 article and index have DOI [`10.5281/zenodo.23057256`](https://doi.org/10.5281/zenodo.23057256); the DOI `10.5281/zenodo.22727368` identifies the earlier v1.0.1 PDFs.

Existing public download entry, from a fixed checkout:

```sh
python3 scripts/fetch.py --list
python3 scripts/fetch.py --group analytic --group upstream --group x --group b
```

`docs/DOWNLOADS.md` lists archive identities, sizes and environment allowances; `manifests/release-assets.json` binds transport objects; `manifests/verifier-source-map.json` indexes the source mirror. Run the complete original archive, not a source-only mirror with missing data. A fetch or hash-check result establishes byte identity only.

The original published inventory is 4,494,382,372 bytes, with deliberate overlap. The two negative-diagonal archives contain about 21.54 GB of outer uncompressed files. Runtime expansion, verification output, dependencies and caches are additional. The public guide's 50 GB free-disk and 32 GB RAM allowances for the full exact collection are planning allowances, not measured minimum requirements.

The [30 September selective assembly preflight](../provenance/v102_assembly_preflight/README.md) checked the complete compressed hashes of the two B archives, extracted 706 required members directly into a new directory with individual hash checks, and reproduced the 570-job, 566-target dependency plan. This tests the public-byte entrance within its selected scope. It does not replace full archive extraction, execution of the 570 mathematical tasks, the original-root verifier or the upstream dependencies.

## Complete X component entries

Run each from the stated extracted package root, retaining the archive's own model, inputs and frozen code. Do not mix same-named verifiers from different archives.

| Domain | Archive | Entry |
|---|---|---|
| `0 < k ≤ 2` | `rho5_v31_exact.zip` | In package root: `python3 verify_all.py` |
| `k ≥ 2.2` | `ROUND43_MINIMAL_REPLAY.zip` | In `RHO5_CQG_ROUND43/`: `bash repro/replay.sh` |
| `2.15 ≤ k ≤ 2.2` and strict high-r for `2.1 ≤ k ≤ 2.2` | `ROUND44_MINIMAL_REPLAY.zip` | In `ROUND44_MINIMAL_REPLAY/`: `python3 repro/replay_new.py .` |
| `2.14 ≤ k ≤ 2.15`, `r ≤ k` | `rho5_v33_exact.zip` | In `rho5_v33_exact/`: `python3 verify_all.py` |
| `2.1 ≤ k ≤ 2.14`, `r ≤ k` | `RHO5_ROUND45_EXACT.zip` | In `rho5_round45_exact/`: `python3 replay.py` |
| `2 < k ≤ 2.1`, `r > k` | `RHO5_V34_HIGH_EXACT_FULL.zip` | In `rho5_v34_high/`: `python3 replay_high.py` |
| `gamma/2 ≤ k ≤ 2.1`, `r ≤ k`, `F ≥ gamma` | `RHO5_ROUND47_ALPHA_FULL.zip` | In `rho5_round47_alpha/`: `python3 replay.py` |

Follow the component README for Python/SymPy, C++17 and Boost.Multiprecision versions and supported overrides. Round43 supports `RHO5_PYTHON`/`BOOST_INCLUDE`; Round44 supports `--boost-include`. The corrected strict-high-r implementation is the one inside the full Round46 archive. Historical compatibility notes, including V31 compiler-name compatibility, do not authorize changing a mathematical acceptance rule.

## Original negative-diagonal root

Archive: `historical_root.tar.gz`. The five transport pieces reconstruct its original bytes; they are not mathematical subdomains.

From `rho5_independent_acceptance_20260911_11/`:

```sh
python3 -B -S runtime/r54_replay.py \
  --tree checkpoint/B17_ROOT.json \
  --out REPLAY_ROOT_NEW.json \
  --workers 8 --backend fraction --allow-open
```

Use a new output file. The frozen runtime first verifies `runtime/R54_SOURCE_MANIFEST.json` (959 sources), then checks the actual root terminals, including the enclosed B44 coverage, with exact cross-checks. Use Python without `-O`; `PYTHONOPTIMIZE` must be unset. No LP discovery run or new certificate search is required.

Expected intermediate scope:

```text
PARTIAL_EXACT_COVERAGE_ONLY
nodes = 749693
splits = 374846
contradiction terminals = 374839
alpha-safe terminals = 4
open original-root positions = 4
internal B44 open terminals = 0
```

The exact root bytes have SHA-256 `8e138dce9a65e49252a1f4714229b1ca95227943913f1eeefdf51714810a563c`. The existing cold receipt has SHA-256 `55f3a9dd5090cfd9e21c479444d5cca1fc15fde2b5c22b8180bbd1c834156b37`. The four remaining positions are precisely the ones paid by the independent parent proofs below. `--allow-open` is scoped to this intermediate object, not permission to leave the final proof incomplete.

## Parent mathematics and source composition

Under `rho5_deep500_all_open_20260910_08/` in `final_cover.tar.gz`, the following are real Python interfaces, not command-line recipes:

- `deep_math.load_protocol(deep_root)` loads the frozen depth-500 protocol and verifies its source manifest.
- `deep_math.verify_branch(root, parent, deep_base, projected, target)` checks the actual continuation/projection source and invokes the exact branch verifier with cross-checks. The designated target must be fully covered; unrelated open positions must retain their explicitly scoped meaning.
- After `alpha_cover.configure(b14_runtime)`, `alpha_cover.verify_cut(bp, parent_source, certificate_source, centers, prefix_cache=None)` replays the full source-to-cut mathematics and ancestor-image checks. A serialized outer box is not accepted as proof of the actual source image.

`alpha_parent_cover.py` then consumes these mathematical acceptance records and checks their binding to the complete frozen target set. It is not a replacement for the above mathematical calls. In particular, record fields saying `mathematical_replay_performed = true` identify the producer's run; inspecting those fields does not perform that run anew.

| Parent index | Actual original-root path | Required constituent targets |
|---:|---|---:|
| 338726 | `10011000010101010` | 111 |
| 435003 | `10111000001100011000010111011` | 240 |
| 563285 | `1101000101111` | 159 |
| 675104 | `1110101001111` | 56 |

For each parent, the target-path set must equal the complete original frozen set with no omitted or duplicate path. All transformed sources require the actual ancestor map. A local path is not simply concatenated onto an unrelated original-root path.

The final mathematical anchor can be checked independently using `rho5-final-anchor-example.zip`:

```sh
python3 -S restore_inputs.py
python3 -S verify_joint_anchor.py \
  --v53-dir rho5_v53_exact \
  --b16-dir B_STRUCTURE_16_DELIVERY \
  --output-dir replayed_anchor
```

`replayed_anchor` must be absent or empty. Python 3.10+ and the standard library suffice for this particular package. The expected result is `COMPLETE_ANCHOR_ALPHA_SAFE`, parent `435003`, anchor path `10011101`, `paid_leaves = 54`, `remaining_sources = []`, and `whole_parent_closed = whole_B_closed = false`. The latter flags are intentional: this result covers one final constituent in one parent.

The last composer is `rho5_b16_v53_closure_20260911_18/final_overlay_accept.py`. Its CLI accepts `--config` and `--config-sha256`. The historical configuration is not a portable fresh-replay configuration: it contains original absolute paths, restricts them to `/root/microscope_ws/`, refuses to overwrite completed outputs, and requires the frozen 239/240 baseline for parent 435003. An independent replay must explicitly map those locations, preserve original mathematical identities, bind newly generated records and use fresh output paths. Disabling path/source checks is not a reproduction method.

Required final result:

```text
ACTUAL_ROOT_ALL_OPEN_PARENTS_COVERED
old_root_open_count = 4
effective_open_count = 0
complete_parents = 469
old_frozen_rule_root_modified = false
new_math_replayed_by_this_composer = false
```

The 566 constituent targets cover four root obligations; they are not 566 original parents. Final original-parent accounting is `465 + 4 = 469`. A terminal may establish alpha safety without excluding the stronger `F ≥ gamma` hypothesis. Complete coverage uses the mixed-threshold lemma, not uniform gamma infeasibility.

## Fresh replay versus record audit

A **fresh complete mathematical replay** regenerates every required component acceptance, including the inherited closed complements and all four parent mathematics, before composing their source-bound conclusions. A **record-and-composition audit** checks the preserved acceptance identities, their scopes and their source bindings. Label each result by the work actually performed.

The archives document component acceptances and the final composition. The accompanying 30 September replay now supplies and has executed the negative-diagonal producer plan, explicit location mapping and fresh source-bound composition, including the inherited closed complements and the original root. A tested, location-independent driver that regenerates the entire transitive chain, including upstream V24/V28 and complete-X dependencies, in one fresh environment is still not supplied. The remaining full-chain obligation is to extend and validate this coverage to every retained upstream dependency and run the complete chain in that environment. Merely rerunning the final composer or checking its 357 direct file dependencies does not achieve that scope. The lack of this full-chain driver does not imply that the recorded component computations were never executed.

## Acceptance and failure conditions

Keep mathematical input bytes immutable and use a distinct output location. For every executed component record:

1. Release/commit, asset and input hashes, producer identity and exact invocation.
2. Python/compiler/library versions, operating system, processor model, worker count, elapsed wall time and any measured CPU/memory/disk use.
3. Exact theorem scope, terminal semantics, open targets, source bindings and all recursive dependencies used.
4. Exit status plus full acceptance output; successful file creation alone is insufficient.

A proposed complete replay fails if an input is absent or hash-mismatched; a model/source is changed; assertions are disabled; a guard is not established on the whole box; nonnegative weights or rational bounds fail; a transport is applied outside its qualification; target paths are missing/duplicated; actual root boxes do not match; or any final target remains unpaid. Expected intermediate O records are acceptable only when their complete, identified downstream covers are also checked.

## Trust set and Lean scope

The computer-assisted proof trusts the written analytic arguments, the exact acceptors' implementations (including parsing, row generation, interval bounds and conditional guards), and source/coverage composition. Exact rational arithmetic removes rounding uncertainty; it does not prove that an implementation selected the correct rows or covered the intended source. Discovery optimizers and floating-point search output are not trusted proof terminals.

The first-phase Lean project has its separately recorded project cold rebuild and retains `XGlobalSafety` and `RootEndpointSafety` as explicit assumptions of the sharp endpoint. The B366 second-phase archive contains 1,452 accepted modules and source/progress evidence, but it is a **source review snapshot**, not a standalone build archive: project configuration and parts of the first-phase import closure are omitted. Its limited concrete certificate instances and additional lemmas do not amount to kernel verification of the complete large trees or removal of the two global assumptions. This protocol does not resume that deferred work.

## Recorded timing and resource scope

| Recorded run | Elapsed wall time | Exact scope |
|---|---:|---|
| V24 full-chain fresh-directory replay, 12 September 2026 | 862.85 s | 22 V20/V22/V24 trees plus invoked nested checks; not whole theorem |
| V28 fresh-directory replay, 12 September 2026 | 44.94 s | Eleven required modules and thirteen localization grafts; not all upstream trees |
| Original negative-diagonal root, Linux X, eight Fraction workers | 22,815.35 s (6.34 h) | Original root, including specified four open positions; excludes four parent completions |
| Fresh original negative-diagonal root, existing Linux X host, sixteen Fraction workers, 30 September 2026 | 12,965.7057178 s (about 3 h 36 min) | Fresh original-root verification; excludes the parent producers and final composition |
| Final 54-terminal anchor on X | 184.37 s | Named joint anchor only; excludes whole parent and whole root |

The historical root acceptance record fixes eight processes and the Fraction backend; the new 30 September root run used sixteen Fraction workers. The new root run records an AMD EPYC 7K62 48-Core Processor model, but no run-linked peak-memory measurement is supplied. No hardware-normalized timing is claimed. None of these times is a sum of process CPU seconds, a total discovery cost, or a guaranteed third-party runtime. They should not be added and represented as a measured full-proof replay.


## Completed negative-domain replay (30 September)

The accompanying v1.0.2 replay ZIP's `replay_engineering/` directory supplements the historical interfaces with an executable plan, path mapping, unchanged-acceptor drivers, source-bound fresh composition and twelve executed rejection checks. Start with `replay_engineering/CURRENT_REPLAY_STATUS.md` for the supported preparation/commands and final execution status, and `replay_engineering/x_return/final_20260930/ROOT_FRESH_COMPLETE.json` for the completed composition receipt.

The sealed parent plan contains 566 original targets and four inherited whole-anchor complements, covered by 570 mathematical producer calls. All 570 succeeded. Each source and target is bound to the frozen original records, and a separate fresh Fraction run checked the original root. The four parents accepted 111/111, 240/240, 159/159 and 56/56 targets, respectively. At 15:25:49 Beijing time, the final receipt recorded `FRESH_FOUR_PARENT_AND_ORIGINAL_ROOT_COMPOSITION_ACCEPTED`, `old_root_open_count = 4`, `effective_open_count = 0` and `complete_parents = 469`.

The included `replay_engineering/x_return/final_20260930/FINAL_REPLAY_RECEIPTS_20260930.tar.gz` is 1,951,520 bytes, with SHA-256 `24f85c5ec1128409bdd1c15015d7f2227755f3ac61ef1f322270166ff40aefab`. The accompanying `FINAL_RECEIPT_LOCAL_AUDIT.json` records successful local checks of the hashes and sizes of 628 archive files and the links from all 570 producer receipts to the final result. These transfer and linkage checks validate the returned evidence; they do not rerun its mathematics.

The run used an isolated directory on the existing X Linux host and the frozen acceptors. Previously completed V24/V28 and complete-X acceptances remain retained upstream inputs; their entire dependency chain was not rerun. The long inherited-complement check ran concurrently with the other parent producers, preserving the same frozen driver and plan. Composition required all 570 producer results, source/target identity, actual root paths/boxes and the four expected intermediate OPEN records. The completed result is explicitly scoped to the **negative-diagonal finite cover conditional on the retained upstream analytic and complete-X arguments**. It does not constitute a fresh whole-theorem replay on a new machine, independent implementation of the verifier, or Lean discharge of the two safety assumptions.

The final status supersedes the earlier 14/570 running snapshot. Failed attempts and their errors remain separate from the successful final receipts. Any later replay must inspect job state, use a distinct output directory, and preserve the sealed plan and producer identities. Preparation, small examples and rejection tests alone would not establish completion; the present completion statement is based on all required producer results, the fresh root acceptance and their strict final composition.


## Interpreting the additional records

570 successful producers means success under the prescribed acceptance conditions. The four whole-anchor complements intentionally retain 111/240/159/56 OPEN paths; they are completed through the matching accepted target covers and actual-root binding. It does not mean 570 independently closed domains. The internal root timer is 12952.261012431933 seconds; the launcher interval is 12965.705717802048 seconds, including overhead (difference 13.444705370115 seconds). The receipt tar contains 628 indexed payload files plus EXPORT_MANIFEST.json itself, for 629 regular files.

The historical field remaining_producer_count=565 describes the dispatch after five canaries (570-5), not the present unfinished count; the completed count is 570 and no producer remains unpaid. Historical inputs copied under fresh/joint remain inputs, not fresh proof results. The original executed run_root launcher has SHA-256 c0997cbfd2e9eafa5dc6ab8ee39165f60815224141eab0724f3121eae3142055; consult the full hashes in the preserved files/manifest. The separately supplied run_root.py is a later hardened launcher and must not be represented as the originally executed bytes. The earlier internal DRIVER_REVIEW.md is not included in the public replay ZIP and retains only its historical static-review scope.

The separately dated postrun_audit/ and source_binding/ supplements do not alter the frozen run. The alpha-binding audit checks 512 status/path/source bindings and rejects three in-memory mutations. The historical complement receipts did not serialize actual OPEN-path lists, so newly exported planned path-set hashes are not independent reconstruction of those actual paths. Source-binding data show four exact boxes and 566 target members; the small check does not replay root topology or mathematical terminals. The executed drivers, sealed plan, large certificates and receipt tar remain unchanged.

The original B366 archive had 1,456 members: 1,452 Lean sources and four other files. Adding four support sources produces 1,456 Lean sources; those two uses of 1,456 count different things. The source-only addition does not claim a new full-project build or completion of Lean's global safety obligations.
