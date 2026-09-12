import Rho5.ExternalFourthPivot.Main
import Rho5.ExternalThreePivot.MatrixEnvelope

/-!
# Sharp first-three readouts on the same arbitrary path

The 9/4 result is not inferred from the `peak ≤ 4` branch. We restrict the actual
first two Schur operations to the already defined `firstNested M` and use D83.
Only positivity of the second pivot is needed; the third and fourth may vanish.
-/
namespace Rho5.ExternalFourthPivot

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 p k)

/-- The actual firstNested second Schur pivot, with the zero-denominator branch qualified. -/
theorem nested_thirdMagnitude_eq_abs_k (M : Matrix5) (h00 : M 0 0 = 1)
    (hp : p M ≠ 0) :
    ExternalThreePivot.thirdMagnitude (NestedThreePivot.firstNested M) = |k M| := by
  have hfirst : Pivot.fixedSchur (NestedThreePivot.firstNested M) 0 0 = p M := by
    rw [NestedThreePivot.firstNested_fixedSchur_apply M h00 0 0]
    simpa only [NestedThreePivot.fin2_castSucc_castSucc_zero4]
      using PrefixBorderedMinors.m2_zero_zero M h00
  change (if Pivot.fixedSchur (NestedThreePivot.firstNested M) 0 0 = 0 then 0
    else |Pivot.fixedSchur (Pivot.fixedSchur (NestedThreePivot.firstNested M)) 0 0|) = |k M|
  rw [hfirst, if_neg hp, NestedThreePivot.firstNested_secondSchur_zero_zero M h00]

/-- Third readout ≤9/4 for positive-leading traces, without positive third/fourth premises. -/
theorem positive_leading_third_le_nine_quarters
    (M : Matrix5) (values : List ℝ) (hmax : matrixEntryMax M = 1)
    (h00 : M 0 0 = 1) (htrace : LeadingSigns.LeadingTracePos M values) :
    values.getD 2 0 ≤ (9 : ℝ) / 4 := by
  cases htrace with
  | zeroStop hz => norm_num
  | step hcp0 hne0 hpos0 htail1 =>
      cases htail1 with
      | zeroStop hz => norm_num
      | step hcp1 hne1 hpos1 htail2 =>
          have hp : 0 < p M := hpos1
          have hS4 : Pivot.IsCompletePivot (S4 M) 0 0 := hcp1
          have hm2 : ∀ i j : Fin 4,
              |PrefixBorderedMinors.m2 M i j| ≤ MinorCPDomain.A M :=
            (MinorCPDomain.isCompletePivot_iff_m2 M h00 hp).mp hS4
          have hent : ∀ i j : Fin 5, |M i j| ≤ 1 := by
            intro i j
            rw [← hmax]
            exact MatrixNormalization.abs_entry_le_matrixEntryMax M i j
          have hthree : ExternalThreePivot.FixedOrderNormalized3
              (NestedThreePivot.firstNested M) :=
            NestedThreePivot.firstNested_normalized M h00 hp hent hm2
          have hbound := ExternalThreePivot.fixed_order_three_pivot_le_nine_quarters
            (NestedThreePivot.firstNested M) hthree
          rw [nested_thirdMagnitude_eq_abs_k M h00 (ne_of_gt hp)] at hbound
          have hread : _ = |k M| := leading_first_readout
            (LeadingSigns.leadingLegalTrace_of_leadingTracePos htail2)
          simpa only [List.getD_cons_succ, hread] using hbound

/-- Uniform sharp third-pivot bound on every normalized original path. -/
theorem normalized_third_pivot_le_nine_quarters
    (A : Matrix5) (values : List ℝ) (hmax : matrixEntryMax A = 1)
    (htrace : CompletePivotPath.LegalTrace A values) :
    values.getD 2 0 ≤ (9 : ℝ) / 4 := by
  obtain ⟨M, hMmax, hM00, hpositive⟩ :=
    exists_normalized_positive_matrix A values hmax htrace
  exact positive_leading_third_le_nine_quarters M values hMmax hM00 hpositive

/-- Strong normalized interface: exactly the requested 1, 2, 9/4, 4 readout packet. -/
theorem normalized_early_pivots
    (A : Matrix5) (values : List ℝ) (hmax : matrixEntryMax A = 1)
    (htrace : CompletePivotPath.LegalTrace A values) :
    values.getD 0 0 = 1 ∧
      values.getD 1 0 ≤ 2 ∧
      values.getD 2 0 ≤ (9 : ℝ) / 4 ∧
      values.getD 3 0 ≤ 4 := by
  have hfirst := first_readout_eq_entryMax A values (ne_zero_of_entryMax_eq_one A hmax) htrace
  have hsecond := readout_le_pow_mul_entryMax A values htrace 1
  rw [hmax] at hfirst hsecond
  refine ⟨hfirst, ?_, normalized_third_pivot_le_nine_quarters A values hmax htrace,
    normalized_fourth_pivot_le_four A values hmax htrace⟩
  simpa using hsecond

/-- Sharp third-pivot inequality at original scale, on the same input value list. -/
theorem third_pivot_le_nine_quarters_mul_entryMax
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : CompletePivotPath.LegalTrace A values) :
    values.getD 2 0 ≤ ((9 : ℝ) / 4) * matrixEntryMax A := by
  have hntrace := (CompletePivotPath.legalTrace_normalize_iff A hne values).mpr htrace
  have h := normalized_third_pivot_le_nine_quarters (MatrixNormalization.normalize A)
    (values.map (fun v => (matrixEntryMax A)⁻¹ * v))
    (MatrixNormalization.matrixEntryMax_normalize A hne) hntrace
  rw [getD_map_mul] at h
  exact restore_readout_bound (MatrixNormalization.matrixEntryMax_pos A hne) h

/-- All four sharp upper bounds, without normalization of the input matrix. -/
theorem early_pivot_bounds
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : CompletePivotPath.LegalTrace A values) :
    values.getD 0 0 = matrixEntryMax A ∧
      values.getD 1 0 ≤ 2 * matrixEntryMax A ∧
      values.getD 2 0 ≤ ((9 : ℝ) / 4) * matrixEntryMax A ∧
      values.getD 3 0 ≤ 4 * matrixEntryMax A := by
  refine ⟨first_readout_eq_entryMax A values hne htrace, ?_,
    third_pivot_le_nine_quarters_mul_entryMax A values hne htrace,
    fourth_pivot_le_four_mul_entryMax A values hne htrace⟩
  simpa using readout_le_pow_mul_entryMax A values htrace 1

/-- The fully uniform packet includes A=0; all entries of its stopped trace are zero. -/
theorem early_pivot_bounds_including_zero
    (A : Matrix5) (values : List ℝ)
    (htrace : CompletePivotPath.LegalTrace A values) :
    values.getD 0 0 = matrixEntryMax A ∧
      values.getD 1 0 ≤ 2 * matrixEntryMax A ∧
      values.getD 2 0 ≤ ((9 : ℝ) / 4) * matrixEntryMax A ∧
      values.getD 3 0 ≤ 4 * matrixEntryMax A := by
  by_cases hzero : A = 0
  · subst A
    rw [zero_input_trace values htrace]
    have hmax : matrixEntryMax (0 : Matrix5) = 0 :=
      (MatrixNormalization.matrixEntryMax_eq_zero_iff _).mpr rfl
    norm_num [hmax]
  · exact early_pivot_bounds A values hzero htrace

end Rho5.ExternalFourthPivot
