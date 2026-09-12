/-
D18 — the normalized certificate interface
==========================================

**Item 3.** D17's frozen normalization equivalence is plugged into the supremum's
universal property, so that a certificate about *unit entry-max* matrices bounds
`rho5Trace`:

* `rho5Trace_le_iff_normalized (B)` — `rho5Trace ≤ B` exactly when every member of
  `NormalizedGrowthValues` is at most `B` (D17's `bound_growthValues_iff_bound_normalized`
  composed with `rho5Trace_le_iff`);
* `rho5Trace_le_of_normalized_peak_bound` — the concrete certificate form: if every
  legal trace of every unit entry-max `Matrix5` has peak at most `B`, then
  `rho5Trace ≤ B`.  No path existence or uniqueness is assumed beyond the trace
  hypothesis: the certificate is about the traces that actually exist;
* `rho5Trace_le_sixteen_via_normalized` — the `16` bound re-derived through this route
  (D15's normalized sixteen statement), confirming that the coarse bound is reached by
  the normalized certificate interface as well.

The normalization is D08's `normalize`, cited through D17; nothing here redefines it or
introduces a second norm.
-/
import Rho5.Shared.GrowthSupremum.Supremum

namespace Rho5.GrowthSupremum

open Rho5

/-- **Item 3 (normalized equivalence).** The supremum is bounded by `B` exactly when
every *normalized* growth value is bounded by `B`. -/
theorem rho5Trace_le_iff_normalized (B : ℝ) :
    rho5Trace ≤ B ↔ ∀ g ∈ Rho5.GrowthModel.NormalizedGrowthValues, g ≤ B := by
  rw [rho5Trace_le_iff, Rho5.GrowthModel.bound_growthValues_iff_bound_normalized]

/-- **Item 3 (normalized certificate form).** A bound on the peaks of the legal traces
of every unit entry-max matrix bounds `rho5Trace`.

This is the shape a concrete certificate (per-stage growth bound, box certificate, …)
can be plugged into: it quantifies over the traces that exist, not over hypothetical
paths. -/
theorem rho5Trace_le_of_normalized_peak_bound {B : ℝ}
    (h : ∀ (A : Matrix5) (values : List ℝ), matrixEntryMax A = 1 →
      Rho5.CompletePivotPath.LegalTrace A values →
        Rho5.GrowthModel.tracePeak values ≤ B) :
    rho5Trace ≤ B :=
  (rho5Trace_le_iff_normalized B).mpr fun g hg => by
    obtain ⟨A, values, hmax, htrace, rfl⟩ := hg
    exact h A values hmax htrace

/-- **Item 3 (consistency).** The coarse bound `rho5Trace ≤ 16` is re-derived through
the normalized certificate route, using D15's normalized sixteen statement. -/
theorem rho5Trace_le_sixteen_via_normalized : rho5Trace ≤ 16 :=
  (rho5Trace_le_iff_normalized 16).mpr
    fun _ hg => le_sixteen_of_mem_normalizedGrowthValues hg

/-- A `NormalizedGrowthValues` membership certificate is exactly a unit entry-max matrix
with a legal trace and a peak value; recorded here for callers building certificates. -/
theorem mem_normalizedGrowthValues_iff {g : ℝ} :
    g ∈ Rho5.GrowthModel.NormalizedGrowthValues ↔
      ∃ (A : Matrix5) (values : List ℝ),
        matrixEntryMax A = 1 ∧ Rho5.CompletePivotPath.LegalTrace A values ∧
          g = Rho5.GrowthModel.tracePeak values :=
  Rho5.GrowthModel.mem_normalizedGrowthValues_iff

end Rho5.GrowthSupremum
