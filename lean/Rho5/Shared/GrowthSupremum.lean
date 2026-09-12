/-
D18 — public aggregator: growth value set, nonemptiness, bounds and supremum.

`import Rho5.Shared.GrowthSupremum` gives the whole lane:

* `Nonempty`   — the concrete all-ones witness, `GrowthValues.Nonempty` and
  `NormalizedGrowthValues.Nonempty` (using D14's existence);
* `Bounds`     — `1 ≤ g` and `g ≤ 16` for every growth value, `GrowthValues ⊆ [1, 16]`,
  `BddAbove`, and the same on the normalized side;
* `Supremum`   — `rho5Trace := sSup GrowthValues`, `1 ≤ rho5Trace ≤ 16`, the upper-bound
  property `le_rho5Trace`, the universal property `rho5Trace_le_iff`, and `IsLUB`;
* `Normalized` — D17's normalization equivalence plugged into the universal property,
  plus the concrete certificate form `rho5Trace_le_of_normalized_peak_bound`.

Reused unchanged (read-only): `Rho5.GrowthModel.{GrowthValues, NormalizedGrowthValues,
growthRatio, tracePeak, one_le_growthRatio, tracePeak_le, growthValues_eq_normalized,
bound_growthValues_iff_bound_normalized}` (D17), `Rho5.TraceExistence.{exists_legalTrace,
chosenTrace, chosenTrace_spec}` (D14), `Rho5.TraceGrowth.trace_value_le_sixteen` (D15),
`Rho5.CompletePivotPath.LegalTrace` (D13), `Rho5.MatrixNormalization` (D08),
`Rho5.matrixEntryMax` (pilot).

Scope (frozen by the card): the supremum of a path-defined set together with its coarse
bound.  It is **not** claimed that `rho5Trace` equals the manuscript's alpha, that the
supremum is attained, or that the original main theorems are closed; no such statement
is made anywhere in this lane.
-/
import Rho5.Shared.GrowthSupremum.Nonempty
import Rho5.Shared.GrowthSupremum.Bounds
import Rho5.Shared.GrowthSupremum.Supremum
import Rho5.Shared.GrowthSupremum.Normalized
