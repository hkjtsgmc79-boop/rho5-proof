import Rho5.ExternalThreePivot.Envelope
import Rho5.Shared.Pivot

/-! This is the ONLY frozen project module imported by the new source tree.
The CP predicate and Schur update are used unchanged, never redefined. -/
namespace Rho5.ExternalThreePivot

abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ

def FixedOrderNormalized3 (A : Matrix3) : Prop :=
  (∀ i j, |A i j| ≤ 1) ∧ |A 0 0| = 1 ∧
    Rho5.Pivot.IsCompletePivot (Rho5.Pivot.fixedSchur A) 0 0

noncomputable def secondMagnitude (A : Matrix3) : ℝ :=
  |Rho5.Pivot.fixedSchur A 0 0|

noncomputable def lastMagnitude (S : Matrix2) : ℝ :=
  if S 0 0 = 0 then 0 else |Rho5.Pivot.fixedSchur S 0 0|

noncomputable def thirdMagnitude (A : Matrix3) : ℝ :=
  lastMagnitude (Rho5.Pivot.fixedSchur A)

/-- This is an identity of encodings; zero-tail legitimacy is proved below. -/
theorem lastMagnitude_eq_stoppedSchur (S : Matrix2) :
    lastMagnitude S = stoppedSchur (S 0 0) (S 0 1) (S 1 0) (S 1 1) := by
  rfl

theorem first_pivot_ne_zero (A : Matrix3) (hA : FixedOrderNormalized3 A) :
    A 0 0 ≠ 0 := by
  apply abs_pos.mp
  rw [hA.2.1]
  norm_num

theorem first_pivot_is_complete (A : Matrix3) (hA : FixedOrderNormalized3 A) :
    Rho5.Pivot.IsCompletePivot A 0 0 := by
  intro i j
  rw [hA.2.1]
  exact hA.1 i j

theorem secondMagnitude_nonneg (A : Matrix3) : 0 ≤ secondMagnitude A :=
  abs_nonneg _

theorem secondMagnitude_le_two (A : Matrix3) (hA : FixedOrderNormalized3 A) :
    secondMagnitude A ≤ 2 := by
  have H := two_by_two_tail_bound 1 (A 0 0) (A 0 1) (A 1 0) (A 1 1)
    (by norm_num) hA.2.1 (hA.1 0 1) (hA.1 1 0) (hA.1 1 1)
  change |A 1 1 - A 1 0 * A 0 1 / A 0 0| ≤ 2
  simpa only [mul_one] using H

theorem second_zero_implies_zero_tail (A : Matrix3)
    (hA : FixedOrderNormalized3 A) (ht : secondMagnitude A = 0) :
    Rho5.Pivot.fixedSchur A = 0 := by
  have hp : Rho5.Pivot.fixedSchur A 0 0 = 0 := abs_eq_zero.mp ht
  exact funext fun i => funext fun j =>
    Rho5.Pivot.zero_complete_pivot (Rho5.Pivot.fixedSchur A) 0 0 hA.2.2 hp i j

theorem second_zero_implies_third_zero (A : Matrix3)
    (hA : FixedOrderNormalized3 A) (ht : secondMagnitude A = 0) :
    thirdMagnitude A = 0 := by
  have hS := second_zero_implies_zero_tail A hA ht
  simp [thirdMagnitude, lastMagnitude, hS]

theorem positive_second_pivot_qualified (A : Matrix3)
    (ht : 0 < secondMagnitude A) : Rho5.Pivot.fixedSchur A 0 0 ≠ 0 :=
  abs_pos.mp ht

end Rho5.ExternalThreePivot
