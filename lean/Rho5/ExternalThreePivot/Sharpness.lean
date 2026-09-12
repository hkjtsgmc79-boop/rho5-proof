import Rho5.ExternalThreePivot.MatrixEnvelope
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace Rho5.ExternalThreePivot

noncomputable def lowSharp (t : ℝ) : Matrix3 :=
  !![1, 0, 0; 0, t, t; 0, -t, t]

noncomputable def highSharp (t : ℝ) : Matrix3 :=
  !![1, 1, t - 1; 1, -(t - 1), -1; t - 1, -1, 1]

theorem lowSharp_schur (t : ℝ) :
    Rho5.Pivot.fixedSchur (lowSharp t) = !![t, t; -t, t] := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [lowSharp, Rho5.Pivot.fixedSchur]

theorem highSharp_schur (t : ℝ) :
    Rho5.Pivot.fixedSchur (highSharp t) =
      !![-t, -t; -t, 1 - (t - 1)^2] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [highSharp, Rho5.Pivot.fixedSchur] <;> ring

theorem lowSharp_qualified (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    FixedOrderNormalized3 (lowSharp t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [lowSharp, abs_neg, abs_of_nonneg ht0, ht1]
  · norm_num [lowSharp]
  · rw [lowSharp_schur]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [abs_neg]

theorem highSharp_qualified (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t ≤ 2) :
    FixedOrderNormalized3 (highSharp t) := by
  have ht0 : 0 ≤ t := by linarith only [ht1]
  have hc0 : 0 ≤ t - 1 := by linarith only [ht1]
  have hc1 : t - 1 ≤ 1 := by linarith only [ht2]
  have hcc1 := (unit_interval_mul (t - 1) (t - 1) hc0 hc1 hc0 hc1).2
  have hq0 : 0 ≤ 1 - (t - 1)^2 := by nlinarith only [hcc1]
  have hq1 : 1 - (t - 1)^2 ≤ t := by nlinarith only [sq_nonneg (t - 1), ht1]
  have h1t : |1 - t| ≤ 1 := by
    rw [abs_sub_comm, abs_of_nonneg hc0]
    exact hc1
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [highSharp, abs_neg, abs_of_nonneg hc0, hc1, h1t]
  · norm_num [highSharp]
  · rw [highSharp_schur]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [abs_neg, abs_of_nonneg ht0, abs_of_nonneg hq0, hq1]

theorem lowSharp_second (t : ℝ) (ht0 : 0 ≤ t) : secondMagnitude (lowSharp t) = t := by
  unfold secondMagnitude
  rw [lowSharp_schur]
  change |t| = t
  exact abs_of_nonneg ht0

theorem highSharp_second (t : ℝ) (ht1 : 1 ≤ t) : secondMagnitude (highSharp t) = t := by
  have ht0 : 0 ≤ t := by linarith only [ht1]
  unfold secondMagnitude
  rw [highSharp_schur]
  change |-t| = t
  rw [abs_neg, abs_of_nonneg ht0]

theorem lowSharp_third (t : ℝ) (ht0 : 0 ≤ t) : thirdMagnitude (lowSharp t) = 2 * t := by
  unfold thirdMagnitude
  rw [lowSharp_schur]
  change (if t = 0 then 0 else |t - (-t) * t / t|) = 2 * t
  by_cases ht : t = 0
  · simp [ht]
  · rw [if_neg ht]
    have hfield : t - (-t) * t / t = 2 * t := by
      field_simp [ht] <;> ring
    rw [hfield, abs_of_nonneg (mul_nonneg (by norm_num) ht0)]

theorem highSharp_third (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t ≤ 2) :
    thirdMagnitude (highSharp t) = t * (3 - t) := by
  have ht0 : 0 < t := by linarith only [ht1]
  have htne : t ≠ 0 := ne_of_gt ht0
  have hnt : -t ≠ 0 := neg_ne_zero.mpr htne
  unfold thirdMagnitude
  rw [highSharp_schur]
  change (if -t = 0 then 0 else |(1 - (t - 1)^2) - (-t) * (-t) / (-t)|) =
    t * (3 - t)
  rw [if_neg hnt]
  have hfield : (1 - (t - 1)^2) - (-t) * (-t) / (-t) = t * (3 - t) := by
    field_simp [htne] <;> ring
  rw [hfield, abs_of_nonneg (mul_nonneg (le_of_lt ht0) (by linarith only [ht2]))]

theorem low_branch_sharp (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    FixedOrderNormalized3 (lowSharp t) ∧ secondMagnitude (lowSharp t) = t ∧
      thirdMagnitude (lowSharp t) = phi t := by
  refine ⟨lowSharp_qualified t ht0 ht1, lowSharp_second t ht0, ?_⟩
  rw [lowSharp_third t ht0, phi_eq_low t ht1]

theorem high_branch_sharp (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t ≤ 2) :
    FixedOrderNormalized3 (highSharp t) ∧ secondMagnitude (highSharp t) = t ∧
      thirdMagnitude (highSharp t) = phi t := by
  refine ⟨highSharp_qualified t ht1 ht2, highSharp_second t ht1, ?_⟩
  rw [highSharp_third t ht1 ht2, phi_eq_high t ht1]

theorem sharp_nine_quarters_witness :
    ∃ A : Matrix3, FixedOrderNormalized3 A ∧ thirdMagnitude A = (9 : ℝ) / 4 := by
  refine ⟨highSharp ((3 : ℝ) / 2), highSharp_qualified _ (by norm_num) (by norm_num), ?_⟩
  rw [highSharp_third _ (by norm_num) (by norm_num)]
  norm_num

end Rho5.ExternalThreePivot
