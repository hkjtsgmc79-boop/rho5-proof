/-
D18 — every growth value lies in `[1, 16]`
==========================================

**Item 2, the two bounds.**

* lower bound `1 ≤ g`: D17's `one_le_growthRatio` — for a nonzero matrix the head of a
  legal trace is exactly `matrixEntryMax A` (D13), the peak dominates the head, and the
  denominator is positive (D08).
* upper bound `g ≤ 16`: D15's coarse per-stage bound `trace_value_le_sixteen` says every
  recorded value is at most `16 * matrixEntryMax A`; the peak is the smallest nonnegative
  upper bound (D17's `tracePeak_le`), and the ratio divides by the (positive) entry
  maximum.

The same two bounds are recorded for `NormalizedGrowthValues`, where the upper bound is
D15's normalized sixteen statement and the lower bound is transported through D17's
frozen set equality.  `BddAbove` follows immediately, which is what item 2's supremum
needs.
-/
import Rho5.Shared.GrowthSupremum.Nonempty
import Rho5.Shared.TraceGrowth

namespace Rho5.GrowthSupremum

open Rho5

/-! ## Bounds for the growth values -/

/-- **Item 2 (lower bound).** Every growth value is at least `1`. -/
theorem one_le_of_mem_growthValues {g : ℝ} (hg : g ∈ Rho5.GrowthModel.GrowthValues) :
    1 ≤ g := by
  obtain ⟨A, values, hA, htrace, rfl⟩ := hg
  exact Rho5.GrowthModel.one_le_growthRatio hA htrace

/-- **Item 2 (upper bound, the coarse `16`).** Every growth value is at most `16`,
by D15's per-stage bound and D17's peak lemma. -/
theorem le_sixteen_of_mem_growthValues {g : ℝ} (hg : g ∈ Rho5.GrowthModel.GrowthValues) :
    g ≤ 16 := by
  obtain ⟨A, values, hA, htrace, rfl⟩ := hg
  have hpos : 0 < matrixEntryMax A := Rho5.MatrixNormalization.matrixEntryMax_pos A hA
  have hpeak : Rho5.GrowthModel.tracePeak values ≤ 16 * matrixEntryMax A :=
    Rho5.GrowthModel.tracePeak_le
      (mul_nonneg (by norm_num) (Rho5.MatrixNormalization.matrixEntryMax_nonneg A))
      (Rho5.TraceGrowth.trace_value_le_sixteen A htrace)
  rw [Rho5.GrowthModel.growthRatio_eq, div_le_iff₀ hpos]
  exact hpeak

/-- **Item 2 (the interval statement).** `GrowthValues ⊆ [1, 16]`. -/
theorem growthValues_subset_Icc :
    Rho5.GrowthModel.GrowthValues ⊆ Set.Icc (1 : ℝ) 16 :=
  fun _ hg => ⟨one_le_of_mem_growthValues hg, le_sixteen_of_mem_growthValues hg⟩

/-- **Item 2 (boundedness).** `GrowthValues` is bounded above (by `16`). -/
theorem bddAbove_growthValues : BddAbove Rho5.GrowthModel.GrowthValues :=
  ⟨16, fun _ hg => le_sixteen_of_mem_growthValues hg⟩

/-! ## The same bounds on the normalized side -/

/-- Normalized growth values are at least `1` (transported through D17's set equality). -/
theorem one_le_of_mem_normalizedGrowthValues {g : ℝ}
    (hg : g ∈ Rho5.GrowthModel.NormalizedGrowthValues) : 1 ≤ g :=
  one_le_of_mem_growthValues (Rho5.GrowthModel.mem_growthValues_iff_mem_normalized.mpr hg)

/-- **Item 3 (normalized certificate, upper bound).** Normalized growth values are at
most `16`: for a unit entry-max matrix D15's bound reads `v ≤ 16`. -/
theorem le_sixteen_of_mem_normalizedGrowthValues {g : ℝ}
    (hg : g ∈ Rho5.GrowthModel.NormalizedGrowthValues) : g ≤ 16 := by
  obtain ⟨A, values, hmax, htrace, rfl⟩ := hg
  refine Rho5.GrowthModel.tracePeak_le (by norm_num) (fun v hv => ?_)
  have h16 := Rho5.TraceGrowth.trace_value_le_sixteen A htrace v hv
  rwa [hmax, mul_one] at h16

/-- **Item 2/3 (normalized boundedness).** -/
theorem bddAbove_normalizedGrowthValues :
    BddAbove Rho5.GrowthModel.NormalizedGrowthValues :=
  ⟨16, fun _ hg => le_sixteen_of_mem_normalizedGrowthValues hg⟩

end Rho5.GrowthSupremum
