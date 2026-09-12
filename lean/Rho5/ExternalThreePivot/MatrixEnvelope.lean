import Rho5.ExternalThreePivot.SignNormalization

namespace Rho5.ExternalThreePivot

/-- Restores an original entry from the actual first Schur update. -/
theorem first_schur_restore (A : Matrix3) (h00 : A 0 0 = 1) (i j : Fin 2) :
    A i.succ 0 * A 0 j.succ + Rho5.Pivot.fixedSchur A i j = A i.succ j.succ := by
  dsimp [Rho5.Pivot.fixedSchur]
  rw [h00, div_one]
  ring

/-- Actual matrix entries supply every field of the scalar theorem's input.
There are no assumed budget inequalities or assumed final pivot bounds. -/
theorem matrix_to_head_data (A : Matrix3) (hA : FixedOrderNormalized3 A)
    (h00 : A 0 0 = 1)
    (hcol : ∀ i, 0 ≤ A i 0) (hrow : ∀ j, 0 ≤ A 0 j) :
    NormalizedHeadData (A 1 0) (A 2 0) (A 0 1) (A 0 2)
      (Rho5.Pivot.fixedSchur A 0 0) (Rho5.Pivot.fixedSchur A 0 1)
      (Rho5.Pivot.fixedSchur A 1 0) (Rho5.Pivot.fixedSchur A 1 1) := by
  refine {
    x_nonneg := hcol 1
    x_le_one := (le_abs_self _).trans (hA.1 1 0)
    u_nonneg := hcol 2
    u_le_one := (le_abs_self _).trans (hA.1 2 0)
    y_nonneg := hrow 1
    y_le_one := (le_abs_self _).trans (hA.1 0 1)
    v_nonneg := hrow 2
    v_le_one := (le_abs_self _).trans (hA.1 0 2)
    entry11 := ?_
    entry12 := ?_
    entry21 := ?_
    entry22 := ?_
    complete12 := hA.2.2 0 1
    complete21 := hA.2.2 1 0
    complete22 := hA.2.2 1 1 }
  · rw [show A 1 0 * A 0 1 + Rho5.Pivot.fixedSchur A 0 0 = A 1 1
        from first_schur_restore A h00 0 0]
    exact hA.1 1 1
  · rw [show A 1 0 * A 0 2 + Rho5.Pivot.fixedSchur A 0 1 = A 1 2
        from first_schur_restore A h00 0 1]
    exact hA.1 1 2
  · rw [show A 2 0 * A 0 1 + Rho5.Pivot.fixedSchur A 1 0 = A 2 1
        from first_schur_restore A h00 1 0]
    exact hA.1 2 1
  · rw [show A 2 0 * A 0 2 + Rho5.Pivot.fixedSchur A 1 1 = A 2 2
        from first_schur_restore A h00 1 1]
    exact hA.1 2 2

theorem fixed_order_nonnegative_head_envelope (A : Matrix3)
    (hA : FixedOrderNormalized3 A) (h00 : A 0 0 = 1)
    (hcol : ∀ i, 0 ≤ A i 0) (hrow : ∀ j, 0 ≤ A 0 j) :
    0 ≤ secondMagnitude A ∧ secondMagnitude A ≤ 2 ∧
      thirdMagnitude A ≤ phi (secondMagnitude A) := by
  have hdata := matrix_to_head_data A hA h00 hcol hrow
  have H := scalar_three_pivot_envelope
    (A 1 0) (A 2 0) (A 0 1) (A 0 2)
    (Rho5.Pivot.fixedSchur A 0 0) (Rho5.Pivot.fixedSchur A 0 1)
    (Rho5.Pivot.fixedSchur A 1 0) (Rho5.Pivot.fixedSchur A 1 1) hdata
  change 0 ≤ |Rho5.Pivot.fixedSchur A 0 0| ∧
    |Rho5.Pivot.fixedSchur A 0 0| ≤ 2 ∧
    lastMagnitude (Rho5.Pivot.fixedSchur A) ≤ phi |Rho5.Pivot.fixedSchur A 0 0|
  rw [lastMagnitude_eq_stoppedSchur]
  exact H

/-- The requested actual fixed-order 3×3 theorem. The first pivot may be -1,
all first-row/column signs are arbitrary, and tied CP choices are allowed. -/
theorem fixed_order_three_pivot_envelope (A : Matrix3)
    (hA : FixedOrderNormalized3 A) :
    0 ≤ secondMagnitude A ∧ secondMagnitude A ≤ 2 ∧
      thirdMagnitude A ≤ phi (secondMagnitude A) := by
  have hcol : ∀ i, 0 ≤ normalizeHead A i 0 := by
    intro i
    rw [normalizeHead_first_column]
    exact abs_nonneg _
  have hrow : ∀ j, 0 ≤ normalizeHead A 0 j := by
    intro j
    rw [normalizeHead_first_row]
    exact abs_nonneg _
  have H := fixed_order_nonnegative_head_envelope (normalizeHead A)
    (normalizeHead_fixed_order A hA) (normalizeHead_pivot A hA) hcol hrow
  rw [normalizeHead_secondMagnitude A hA, normalizeHead_thirdMagnitude A hA] at H
  exact H

theorem fixed_order_three_pivot_le_nine_quarters (A : Matrix3)
    (hA : FixedOrderNormalized3 A) : thirdMagnitude A ≤ (9 : ℝ) / 4 := by
  obtain ⟨ht0, ht2, hg⟩ := fixed_order_three_pivot_envelope A hA
  exact hg.trans (phi_le_nine_quarters (secondMagnitude A) ht0 ht2)

/-- Explicit endpoint interface: t = 1 is handled without using t > 1. -/
theorem fixed_order_at_one (A : Matrix3)
    (hA : FixedOrderNormalized3 A) (ht : secondMagnitude A = 1) :
    thirdMagnitude A ≤ 2 := by
  have H := (fixed_order_three_pivot_envelope A hA).2.2
  simpa only [ht, phi_one] using H

end Rho5.ExternalThreePivot
