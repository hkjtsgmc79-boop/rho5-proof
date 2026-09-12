import Rho5.Shared.BFibreGlobalEndpoint.Basic
import Rho5.Shared.BFibreGlobalEndpoint.GlobalMax

/-!
# D139 public entry point — the real B-fibre capacity endpoint

Assembly over the accepted D121 capacity layer (`Rho5.ExternalBFibreCapacity`), D87's compiled
pivot bounds, D92's `4 < rho5Trace`, and the frozen `GrowthValues`/`rho5Trace` interface.

Main declarations:

* `four_lt_capF`, `one_le_capF`, `prefixP_le_two`, `prefixP_lt_capF`,
  `k_le_nine_quarters`, `k_lt_capF` — the high-value premise and the paid dominance bounds;
* `canonical_endpoint_normalized` / `_frame` / `_height` / `_dominates` / `_matrix` — the real
  canonical endpoint's `NormalizedB`, frame preservation, height, domination and real-matrix facts
  (`matrixEntryMax = 1`, `LegalTrace`, `PolyCP`, `capF ≤ growthRatio`);
* `capF_le_rho5Trace` — **`capF (frameOf z) ≤ rho5Trace`** for every `NormalizedB z`, through the
  actual reconstruction's membership in `GrowthValues`;
* `growth_eq_capF_of_four_lt` — the actual `growthRatio = capF` under `4 < z 23`;
* `high_value_capacity_endpoint` — the bundled high-value endpoint;
* `capF_eq_rho5Trace`, `four_lt_of_eq_rho5Trace`, `global_max_growth_eq_rho5Trace`,
  `normalizedB_global_max_has_canonical_fibre_endpoint` (**the main interface**) and
  `exists_global_max_canonical_fibre_endpoint` — the global maximizer endpoint at
  `z 23 = rho5Trace`.

Scope: no `alpha` statement (`rho5Trace` is **not** claimed to equal `alpha`), no original-root
proof, no all-`B` coverage, no new numerical search.  The audit module
`Rho5.Shared.BFibreGlobalEndpoint.Audit` is deliberately not imported here.
-/
