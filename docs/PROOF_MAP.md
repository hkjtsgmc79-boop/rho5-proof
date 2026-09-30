# Proof map and trust boundaries

The paper proves the real five-dimensional complete-pivoting growth bound using written analysis and exact computational certificates. The companion Lean project provides an additional formalization of substantial analytic parts. These are related layers, with different verification claims.

| Responsibility | First-phase Lean coverage | External part |
|---|---|---|
| Exact alpha | Root isolation, identity, uniqueness and comparison bounds | Original polynomial/coefficient provenance is retained with the paper materials |
| Attainment | Actual candidate existence, compatibility with alpha, real matrix and legal attaining path | Original reconstruction materials are available for independent comparison |
| General real inputs | Legal-path definitions, early bounds, global maximizer existence and key source-preserving X/B reductions | Written paper specifies all quantifiers and boundaries |
| Local analytic motion | Actual local ODE trajectories and physical resource endpoints, with their starting-region and budget assumptions | A local trajectory is not an automatic global safety proof |
| Global X safety | Explicit `XGlobalSafety` interface | Necessary exact component certificates, analytic rules and remaining source/coverage connections |
| Global B-root safety | Original `RootEndpointSafety` interface | Root/parent/alpha-cover mathematics and complete source-cover composition |
| Sharp final equality | Conditional endpoint from the two original safety hypotheses | Complete kernel discharge of those global hypotheses is outside this first-phase release |

The no-external-safety baseline includes `alpha ≤ rho5Trace ≤ 81/16`. It is distinct from the conditional sharp equality.

The v1.0.2 B366 addition is a **source-only** second-phase review snapshot. It preserves 1,452 accepted Lean sources and adds four identified support sources. Its 57 external direct imports are available across the frozen first-phase base and the additive [76-source dependency supplement](LEAN_PHASE2_SOURCE_ASSEMBLY.md). Static assembly checks the 2,027-module recursive Rho5 source closure; no new combined build or axiom audit is claimed. It does not replace the first-phase cold-build record or prove either global safety interface unconditionally.

See [the detailed Lean coverage catalogue](../lean/docs/COVERAGE.md), [obligations](../lean/docs/OBLIGATIONS.md), [public types](../lean/FINAL_THEOREM_TYPES.txt) and [axiom records](../lean/AXIOMS.json).

## What the exact certificates establish

The frozen acceptors check rational identities, inequalities, qualified analytic rules, source bindings and tree/domain coverage. Some terminal rules exclude a stronger rational-threshold hypothesis, while others prove safety at the exact alpha bound. These must not be conflated. A domain can be alpha-safe without being empty.

The final root preserves four original open records. Separate source-bound covers discharge them. Existing final composition records refer to accepted components and are not themselves a fresh execution of every component checker. The published archives and supplementary index retain that distinction.

On 30 September 2026 the negative-diagonal finite cover was freshly checked on the existing X host: 570 producer calls passed, the original root was rerun with exact Fraction arithmetic, and all four parent covers were bound back to its four original OPEN boxes. The final finite-cover receipt has `effective_open_count = 0`. This result retains upstream analytic and complete-X premises; see the [dated replay guide](REPLAY_20260930.md) for its exact scope and evidence.

## What is trusted in this release

Lean checks the supplied formal statements with their explicit hypotheses and recorded standard axioms. The Python/C++ programs are exact-arithmetic implementations, but their source-code correctness is not claimed to be formally proved. The full paper also relies on its written analytic arguments and the correctness of source/coverage composition.

The release contains no assertion that a Python PASS directly constructs a Lean proof of `XGlobalSafety` or `RootEndpointSafety`. A SHA-256 match establishes file identity, not mathematical correctness. Publishing the archive does not constitute a new cold replay.

## What is deferred

Full-tree Lean instances, a fully verified executable checker, a fresh-machine build of Lean and all third-party dependencies, and a tested single-command complete mathematical replay are not claimed by this release. A cold rebuild of the frozen first-phase project itself has completed with third-party caches reused and supplemented; see [the recorded scope](LEAN_COLD_REBUILD.md). The second-phase source review archive is not included in that default product.

The real-field theorem does not claim a complex-field result or a classification of all maximizing matrices.
