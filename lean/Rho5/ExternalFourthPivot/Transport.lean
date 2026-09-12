import Rho5.ExternalFourthPivot.Readout
import Rho5.Shared.LeadingSigns
import Rho5.Shared.FirstPivotDomain.PivotEntry
import Rho5.Shared.TraceSigns.Normalize

/-!
# Same-list transport to a normalized positive-leading matrix

Only the existing all-path permutation and sign theorems are used. In particular,
no maximizer replacement and no assertion that different tied paths agree is used.
-/
namespace Rho5.ExternalFourthPivot

open Rho5

/-- The first actual observation of a leading trace, including zero-stop. -/
theorem leading_first_readout {n : ℕ}
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {values : List ℝ}
    (h : LeadingTrace.LeadingLegalTrace M values) :
    values.getD 0 0 = |M 0 0| := by
  cases h with
  | zeroStop hz => simp [hz]
  | step hmax hne htail => simp

/-- At order five, a unit-norm positive-leading trace starts at the actual entry 1. -/
theorem positive_leading_entry_eq_one (M : Matrix5) (values : List ℝ)
    (hmax : matrixEntryMax M = 1)
    (h : LeadingSigns.LeadingTracePos M values) : M 0 0 = 1 := by
  have hne : M ≠ 0 := ne_zero_of_entryMax_eq_one M hmax
  cases h with
  | zeroStop hz => exact False.elim (hne hz)
  | step hcp hpne hpos htail =>
      have habs := FirstPivotDomain.matrixEntryMax_eq_abs_of_isCompletePivot hcp
      rw [abs_of_pos hpos, hmax] at habs
      exact habs.symm

/-- Explicit transport: the same list is retained by actual static permutations/signs. -/
theorem exists_normalized_positive_representation
    (A : Matrix5) (values : List ℝ) (hmax : matrixEntryMax A = 1)
    (htrace : CompletePivotPath.LegalTrace A values) :
    ∃ (row col : Equiv.Perm (Fin 5)) (sgn : Fin 5 → ℝ),
      TraceSigns.IsSign sgn ∧
      let M := TraceSigns.signedEntries (TracePermutation.permuteEntries A row col) sgn 1
      matrixEntryMax M = 1 ∧ M 0 0 = 1 ∧
        LeadingSigns.LeadingTracePos M values := by
  obtain ⟨row, col, hleading⟩ := LeadingTrace.exists_permute_leadingLegalTrace htrace
  obtain ⟨sgn, hsgn, hpositive⟩ := LeadingSigns.exists_signs_leadingTracePos hleading
  let B := TracePermutation.permuteEntries A row col
  let M := TraceSigns.signedEntries B sgn 1
  have hone : TraceSigns.IsSign (1 : Fin 5 → ℝ) := fun _ => Or.inl rfl
  have hMmax : matrixEntryMax M = 1 := by
    change matrixEntryMax (TraceSigns.signedEntries5 B sgn 1) = 1
    rw [TraceSigns.matrixEntryMax_signedEntries5 B hsgn hone]
    change matrixEntryMax (TracePermutation.permuteEntries A row col) = 1
    rw [TracePermutation.matrixEntryMax_permuteEntries, hmax]
  have hM00 : M 0 0 = 1 := positive_leading_entry_eq_one M values hMmax hpositive
  exact ⟨row, col, sgn, hsgn, hMmax, hM00, hpositive⟩

/-- Convenient actual matrix version of the explicit same-list representation. -/
theorem exists_normalized_positive_matrix
    (A : Matrix5) (values : List ℝ) (hmax : matrixEntryMax A = 1)
    (htrace : CompletePivotPath.LegalTrace A values) :
    ∃ M : Matrix5, matrixEntryMax M = 1 ∧ M 0 0 = 1 ∧
      LeadingSigns.LeadingTracePos M values := by
  obtain ⟨row, col, sgn, _, hMmax, hM00, hpositive⟩ :=
    exists_normalized_positive_representation A values hmax htrace
  exact ⟨_, hMmax, hM00, hpositive⟩

/-- Scaling, permutations, and signs combined; the whole normalized list is explicit. -/
theorem exists_original_path_representation
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : CompletePivotPath.LegalTrace A values) :
    ∃ (row col : Equiv.Perm (Fin 5)) (sgn : Fin 5 → ℝ),
      TraceSigns.IsSign sgn ∧
      let M := TraceSigns.signedEntries
        (TracePermutation.permuteEntries (MatrixNormalization.normalize A) row col) sgn 1
      matrixEntryMax M = 1 ∧ M 0 0 = 1 ∧
        LeadingSigns.LeadingTracePos M
          (values.map (fun v => (matrixEntryMax A)⁻¹ * v)) := by
  exact exists_normalized_positive_representation
    (MatrixNormalization.normalize A)
    (values.map (fun v => (matrixEntryMax A)⁻¹ * v))
    (MatrixNormalization.matrixEntryMax_normalize A hne)
    ((CompletePivotPath.legalTrace_normalize_iff A hne values).mpr htrace)

end Rho5.ExternalFourthPivot
