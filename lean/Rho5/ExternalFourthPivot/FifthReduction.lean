import Rho5.ExternalFourthPivot.Main

/-! # Readout-preserving reduction of growth above four to the fifth pivot -/
namespace Rho5.ExternalFourthPivot

open Rho5

/-- After D86 transport, the old fourth/fifth disjunction has only its fifth branch. -/
theorem growth_above_four_is_fifth
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : CompletePivotPath.LegalTrace A values)
    (hgrowth : 4 < GrowthModel.growthRatio A values) :
    values.length = 5 ∧
      values.getD 4 0 = GrowthModel.tracePeak values ∧
      4 * matrixEntryMax A < values.getD 4 0 := by
  rcases HighGrowthTail.peak_is_getD_three_or_four A hne htrace hgrowth with
    ⟨_, _, hfour⟩ | ⟨hlen, hfifth, hgt⟩
  · have hbound := fourth_pivot_le_four_mul_entryMax A values hne htrace
    exact False.elim ((not_lt_of_ge hbound) hfour)
  · exact ⟨Nat.le_antisymm (CompletePivotPath.length_le_five htrace) hlen, hfifth, hgt⟩

/-- A downstream cap ≥4 needs only the actual fifth readout of this same path. -/
theorem growth_le_of_fifth_readout_le
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : CompletePivotPath.LegalTrace A values)
    (cap : ℝ) (hcap : 4 ≤ cap)
    (hfifth : values.getD 4 0 ≤ cap * matrixEntryMax A) :
    GrowthModel.growthRatio A values ≤ cap := by
  by_cases hsmall : GrowthModel.growthRatio A values ≤ 4
  · exact hsmall.trans hcap
  · obtain ⟨_, hread, _⟩ := growth_above_four_is_fifth A values hne htrace
      (lt_of_not_ge hsmall)
    rw [GrowthModel.growthRatio_eq]
    apply (div_le_iff₀ (MatrixNormalization.matrixEntryMax_pos A hne)).mpr
    simpa only [hread] using hfifth

end Rho5.ExternalFourthPivot
