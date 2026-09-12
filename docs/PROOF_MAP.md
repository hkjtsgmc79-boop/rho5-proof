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

See [the detailed Lean coverage catalogue](../lean/docs/COVERAGE.md), [obligations](../lean/docs/OBLIGATIONS.md), [public types](../lean/FINAL_THEOREM_TYPES.txt) and [axiom records](../lean/AXIOMS.json).

## What the exact certificates establish

The frozen acceptors check rational identities, inequalities, qualified analytic rules, source bindings and tree/domain coverage. Some terminal rules exclude a stronger rational-threshold hypothesis, while others prove safety at the exact alpha bound. These must not be conflated. A domain can be alpha-safe without being empty.

The final root preserves four original open records. Separate source-bound covers discharge them. Existing final composition records refer to accepted components and are not themselves a fresh execution of every component checker. The published archives and supplementary index retain that distinction.

## What is trusted in this release

Lean checks the supplied formal statements with their explicit hypotheses and recorded standard axioms. The Python/C++ programs are exact-arithmetic implementations, but their source-code correctness is not claimed to be formally proved. The full paper also relies on its written analytic arguments and the correctness of source/coverage composition.

The release contains no assertion that a Python PASS directly constructs a Lean proof of `XGlobalSafety` or `RootEndpointSafety`. A SHA-256 match establishes file identity, not mathematical correctness. Publishing the archive does not constitute a new cold replay.

## What is deferred

Full-tree Lean instances, a fully verified executable checker, a new-machine cold build of the whole Lean source closure, and a tested single-command complete mathematical replay are not claimed by this release. Existing partial Lean tree experiments are not included in the default product.

The real-field theorem does not claim a complex-field result or a classification of all maximizing matrices.
