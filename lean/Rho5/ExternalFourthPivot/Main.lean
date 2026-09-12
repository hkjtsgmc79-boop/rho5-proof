import Rho5.ExternalFourthPivot.NormalizedFourth

/-! # Required original-matrix, original-value-list fourth-pivot interfaces -/
namespace Rho5.ExternalFourthPivot

open Rho5

/-- Fourth actual pivot magnitude, in the scale of the original nonzero matrix. -/
theorem fourth_pivot_le_four_mul_entryMax
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : CompletePivotPath.LegalTrace A values) :
    values.getD 3 0 ≤ 4 * matrixEntryMax A := by
  have hntrace := (CompletePivotPath.legalTrace_normalize_iff A hne values).mpr htrace
  have h := normalized_fourth_pivot_le_four (MatrixNormalization.normalize A)
    (values.map (fun v => (matrixEntryMax A)⁻¹ * v))
    (MatrixNormalization.matrixEntryMax_normalize A hne) hntrace
  rw [getD_map_mul] at h
  exact restore_readout_bound (MatrixNormalization.matrixEntryMax_pos A hne) h

/-- Earlier than the fourth pivot, D15's old bound already suffices. -/
theorem first_three_readouts_le_four_mul_entryMax
    (A : Matrix5) (values : List ℝ)
    (htrace : CompletePivotPath.LegalTrace A values) (j : ℕ) (hj : j < 3) :
    values.getD j 0 ≤ 4 * matrixEntryMax A := by
  have h := readout_le_pow_mul_entryMax A values htrace j
  have hm : 0 ≤ matrixEntryMax A := MatrixNormalization.matrixEntryMax_nonneg A
  have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hjcases with rfl | rfl | rfl <;> norm_num at h ⊢ <;> nlinarith

/-- All four early readouts of the input path; absent entries have default zero. -/
theorem all_early_pivots_le_four_mul_entryMax
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : CompletePivotPath.LegalTrace A values) :
    ∀ j : ℕ, j < 4 → values.getD j 0 ≤ 4 * matrixEntryMax A := by
  intro j hj
  by_cases hj3 : j < 3
  · exact first_three_readouts_le_four_mul_entryMax A values htrace j hj3
  · have hjeq : j = 3 := by omega
    subst j
    exact fourth_pivot_le_four_mul_entryMax A values hne htrace

/-- The zero input is a genuine singleton stop, not an invented five-element trace. -/
theorem zero_input_trace (values : List ℝ)
    (htrace : CompletePivotPath.LegalTrace (0 : Matrix5) values) : values = [0] := by
  exact CompletePivotPath.zero_iff.mp htrace

/-- The fourth-pivot inequality in fact holds for the zero matrix too. -/
theorem fourth_pivot_le_four_mul_entryMax_including_zero
    (A : Matrix5) (values : List ℝ)
    (htrace : CompletePivotPath.LegalTrace A values) :
    values.getD 3 0 ≤ 4 * matrixEntryMax A := by
  by_cases hzero : A = 0
  · subst A
    rw [zero_input_trace values htrace]
    have hmax : matrixEntryMax (0 : Matrix5) = 0 :=
      (MatrixNormalization.matrixEntryMax_eq_zero_iff _).mpr rfl
    simp [hmax]
  · exact fourth_pivot_le_four_mul_entryMax A values hzero htrace

/-- No nonzero or full-rank premise is needed for the uniform early bound. -/
theorem all_early_pivots_le_four_mul_entryMax_including_zero
    (A : Matrix5) (values : List ℝ)
    (htrace : CompletePivotPath.LegalTrace A values) :
    ∀ j : ℕ, j < 4 → values.getD j 0 ≤ 4 * matrixEntryMax A := by
  intro j hj
  by_cases hj3 : j < 3
  · exact first_three_readouts_le_four_mul_entryMax A values htrace j hj3
  · have hjeq : j = 3 := by omega
    subst j
    exact fourth_pivot_le_four_mul_entryMax_including_zero A values htrace

end Rho5.ExternalFourthPivot
