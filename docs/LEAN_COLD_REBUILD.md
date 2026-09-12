# Completed first-phase Lean project cold rebuild

**Completed: 12 September 2026, 21:58 UTC+08:00.** The recorded D162 run rebuilt the frozen RHO5 product on Linux from an empty project-object directory. Its source archive is identical to the published [first-phase source](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/rho5-lean-phase-one.zip).

| Check | Recorded result |
| :--- | :--- |
| Frozen product import closure | 634 / 634 modules |
| Additional example and audit modules | 3 / 3 |
| Named axiom checks | 47 / 47; standard axioms only |
| Final theorem | `XGlobalSafety → RootEndpointSafety → rho5Trace = alpha` |

## Successful route and original failure

The successful run used an explicit dependency-order driver and individual Lean compilations, eventually across six authorized lanes. Lean was fixed at 4.30.0; mathlib was fixed at `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Third-party caches were reused and missing dependencies were supplemented. The recorded session took approximately 4 hours 11 minutes, including recovery and dependency work; this is not a clean benchmark or a prediction for another machine.

The original packaged command `lake build +Rho5.PhaseOne:olean` failed in the cold state because `Conditional.olean` was missing. A Lake discovery configuration revision was not accepted as a completed build. The later driver success must not be described as success of that original command.

The [original Lean build notes](../lean/docs/BUILDING.md) are retained as historical provenance. They precede this cold run. The current [verification guide](VERIFY.md#2-check-the-lean-analytic-development) distinguishes the setup commands, the known failing cold entry, and the accepted route.

## Evidence available here

- [Build status](../paper/data/lean_cold_build/BUILD_STATUS.json), [final receipt](../paper/data/lean_cold_build/COLD_REBUILD_READY.json), and [axiom summary](../paper/data/lean_cold_build/AXIOM_CHECK.json).
- [Bounded independent scope audit](../paper/data/lean_cold_build/SCOPE_AUDIT.md).
- [Original receipt archive](../paper/data/lean_cold_build/D162_COLD_REBUILD_RECEIPTS_20260912.tgz), 107,995 bytes; SHA-256 `c0ec1be2dc8b2aff26f987d13be34a20f0f2e92a4d2389523e9fe88c9c980415`.
- Original frozen source ZIP: SHA-256 `ddb1e4300ed03464024f2a2a227cee060b6b38de96a02043f9233f0412e28f56`.

The retained receipt archive includes the source/object manifest, final gate records, actual axiom/type output and failed-build evidence. It does **not** include all 634 full compilation logs, the Linux objects, or the successful reproduction drivers. It documents the completed run; it is not a standalone cold-rebuild kit.

## What this establishes

This is a project cold rebuild with fixed third-party caches, not a fresh-machine build of Lean and every dependency. The two safety parameters remain assumptions of the sharp Lean theorem. The large certificate stage was not replayed by this run; the external Python/C++ acceptors are not claimed to have been formally verified.
