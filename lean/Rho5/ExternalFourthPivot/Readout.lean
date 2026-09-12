import Rho5.Shared.HighGrowthTail
import Rho5.Shared.CompletePivotPath.Normalize
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Zero-padded observations of the actual input trace (Rev01, 2026-09-12)

`getD` reads the original list; we never replace a stopped trace by a full trace.
These small adapters also cover the empty list and singleton zero-stop list.
-/
namespace Rho5.ExternalFourthPivot

open Rho5

/-- Every zero-default readout is bounded by the peak, even out of range. -/
theorem getD_le_tracePeak (values : List ℝ) (j : ℕ) :
    values.getD j 0 ≤ GrowthModel.tracePeak values := by
  induction values generalizing j with
  | nil => simp [GrowthModel.tracePeak]
  | cons a tail ih =>
      cases j with
      | zero => simpa only [List.getD_cons_zero, GrowthModel.tracePeak_cons]
          using (le_max_left a (GrowthModel.tracePeak tail))
      | succ j =>
          simpa only [List.getD_cons_succ, GrowthModel.tracePeak_cons]
            using (ih j).trans (le_max_right a (GrowthModel.tracePeak tail))

/-- Out-of-range observations are exactly the specified default zero. -/
theorem getD_zero_of_length_le (values : List ℝ) (j : ℕ)
    (hj : values.length ≤ j) : values.getD j 0 = 0 := by
  induction values generalizing j with
  | nil => simp
  | cons a tail ih =>
      cases j with
      | zero => simp at hj
      | succ j =>
          have ht : tail.length ≤ j := by simpa using hj
          simpa only [List.getD_cons_succ] using ih j ht

/-- Scaling the *whole* value list commutes with zero-default observation. -/
theorem getD_map_mul (values : List ℝ) (j : ℕ) (c : ℝ) :
    (values.map (fun v => c * v)).getD j 0 = c * values.getD j 0 := by
  induction values generalizing j with
  | nil => simp
  | cons a tail ih =>
      cases j with
      | zero => simp
      | succ j => simpa using ih j

/-- D15's existing in-range estimate, with the real zero-stop convention. -/
theorem readout_le_pow_mul_entryMax (A : Matrix5) (values : List ℝ)
    (htrace : CompletePivotPath.LegalTrace A values) (j : ℕ) :
    values.getD j 0 ≤ (2 : ℝ) ^ j * matrixEntryMax A := by
  by_cases hj : j < values.length
  · rw [HighGrowthTail.getD_eq_get_of_lt hj]
    exact HighGrowthTail.values_get_le_pow A htrace ⟨j, hj⟩
  · rw [getD_zero_of_length_le values j (Nat.le_of_not_gt hj)]
    exact mul_nonneg (pow_nonneg (by norm_num) j)
      (MatrixNormalization.matrixEntryMax_nonneg A)

/-- This observation remains valid for arbitrary original magnitude lists. -/
theorem first_readout_eq_entryMax (A : Matrix5) (values : List ℝ)
    (hne : A ≠ 0) (htrace : CompletePivotPath.LegalTrace A values) :
    values.getD 0 0 = matrixEntryMax A := by
  cases values with
  | nil => exact False.elim (CompletePivotPath.ne_nil_of_pos htrace rfl)
  | cons a tail =>
      simpa only [List.getD_cons_zero]
        using CompletePivotPath.head_eq_matrixEntryMax hne htrace

/-- A normalized matrix is nonzero; no rank or later-pivot premise is involved. -/
theorem ne_zero_of_entryMax_eq_one (A : Matrix5) (hmax : matrixEntryMax A = 1) :
    A ≠ 0 := by
  intro hz
  have h0 : matrixEntryMax A = 0 :=
    (MatrixNormalization.matrixEntryMax_eq_zero_iff A).mpr hz
  linarith

/-- Positive inverse-scaling can be cancelled after observing the same index. -/
theorem restore_readout_bound {m v b : ℝ} (hm : 0 < m)
    (h : m⁻¹ * v ≤ b) : v ≤ b * m := by
  have h' := mul_le_mul_of_nonneg_left h hm.le
  have hmne : m ≠ 0 := ne_of_gt hm
  calc
    v = m * (m⁻¹ * v) := by rw [← mul_assoc, mul_inv_cancel₀ hmne, one_mul]
    _ ≤ m * b := h'
    _ = b * m := mul_comm _ _

end Rho5.ExternalFourthPivot
