import Rho5.ExternalThreePivot.MatrixDefinitions

namespace Rho5.ExternalThreePivot

/-- A genuine ±1 choice. At zero its value is 1; it never divides by |x|. -/
noncomputable def unitSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem unitSign_abs (x : ℝ) : |unitSign x| = 1 := by
  unfold unitSign
  split <;> norm_num

theorem unitSign_mul_self (x : ℝ) : unitSign x * unitSign x = 1 := by
  unfold unitSign
  split <;> norm_num

theorem unitSign_mul (x : ℝ) : unitSign x * x = |x| := by
  by_cases hx : 0 ≤ x
  · simp [unitSign, hx, abs_of_nonneg hx]
  · simp [unitSign, hx, abs_of_neg (lt_of_not_ge hx)]

@[simp] theorem unitSign_zero : unitSign 0 = 1 := by norm_num [unitSign]

theorem ne_zero_of_abs_one (x : ℝ) (hx : |x| = 1) : x ≠ 0 := by
  apply abs_pos.mp
  rw [hx]
  norm_num

noncomputable def signedMatrix {ι κ : Type*}
    (A : Matrix ι κ ℝ) (row : ι → ℝ) (col : κ → ℝ) : Matrix ι κ ℝ :=
  fun i j => row i * A i j * col j

theorem signedMatrix_abs {ι κ : Type*}
    (A : Matrix ι κ ℝ) (row : ι → ℝ) (col : κ → ℝ)
    (hr : ∀ i, |row i| = 1) (hc : ∀ j, |col j| = 1) (i : ι) (j : κ) :
    |signedMatrix A row col i j| = |A i j| := by
  change |row i * A i j * col j| = |A i j|
  rw [abs_mul, abs_mul, hr i, hc j, one_mul, mul_one]

/-- Exact preservation of the non-strict CP predicate, hence of all ties. -/
theorem signedMatrix_complete_iff {ι κ : Type*}
    (A : Matrix ι κ ℝ) (row : ι → ℝ) (col : κ → ℝ)
    (hr : ∀ i, |row i| = 1) (hc : ∀ j, |col j| = 1) (p : ι) (q : κ) :
    Rho5.Pivot.IsCompletePivot (signedMatrix A row col) p q ↔
      Rho5.Pivot.IsCompletePivot A p q := by
  constructor <;> intro h i j
  · simpa only [signedMatrix_abs A row col hr hc] using h i j
  · simpa only [signedMatrix_abs A row col hr hc] using h i j

/-- Actual Schur equivariance. Nonzero pivot qualifications are explicit. -/
theorem fixedSchur_signedMatrix {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (row col : Fin (n + 1) → ℝ)
    (hA : A 0 0 ≠ 0) (hr : row 0 ≠ 0) (hc : col 0 ≠ 0) :
    Rho5.Pivot.fixedSchur (signedMatrix A row col) =
      signedMatrix (Rho5.Pivot.fixedSchur A)
        (fun i => row i.succ) (fun j => col j.succ) := by
  funext i j
  dsimp [Rho5.Pivot.fixedSchur, signedMatrix]
  field_simp [hA, hr, hc] <;> ring

/-- The second elimination also commutes with signs; the zero-stop branch
is dealt with separately, so no elimination step is asserted at a zero pivot. -/
theorem lastMagnitude_signedMatrix (S : Matrix2) (row col : Fin 2 → ℝ)
    (hr : ∀ i, |row i| = 1) (hc : ∀ j, |col j| = 1) :
    lastMagnitude (signedMatrix S row col) = lastMagnitude S := by
  by_cases hS : S 0 0 = 0
  · simp [lastMagnitude, signedMatrix, hS]
  · have hr0 : row 0 ≠ 0 := ne_zero_of_abs_one _ (hr 0)
    have hc0 : col 0 ≠ 0 := ne_zero_of_abs_one _ (hc 0)
    have hscaled : signedMatrix S row col 0 0 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hr0 hS) hc0
    simp only [lastMagnitude, if_neg hscaled, if_neg hS]
    rw [fixedSchur_signedMatrix S row col hS hr0 hc0]
    exact signedMatrix_abs (Rho5.Pivot.fixedSchur S)
      (fun i => row i.succ) (fun j => col j.succ)
      (fun i => hr i.succ) (fun j => hc j.succ) 0 0

theorem secondMagnitude_signedMatrix (A : Matrix3) (row col : Fin 3 → ℝ)
    (hA : A 0 0 ≠ 0) (hr : ∀ i, |row i| = 1) (hc : ∀ j, |col j| = 1) :
    secondMagnitude (signedMatrix A row col) = secondMagnitude A := by
  unfold secondMagnitude
  rw [fixedSchur_signedMatrix A row col hA
    (ne_zero_of_abs_one _ (hr 0)) (ne_zero_of_abs_one _ (hc 0))]
  exact signedMatrix_abs (Rho5.Pivot.fixedSchur A)
    (fun i => row i.succ) (fun j => col j.succ)
    (fun i => hr i.succ) (fun j => hc j.succ) 0 0

theorem thirdMagnitude_signedMatrix (A : Matrix3) (row col : Fin 3 → ℝ)
    (hA : A 0 0 ≠ 0) (hr : ∀ i, |row i| = 1) (hc : ∀ j, |col j| = 1) :
    thirdMagnitude (signedMatrix A row col) = thirdMagnitude A := by
  unfold thirdMagnitude
  rw [fixedSchur_signedMatrix A row col hA
    (ne_zero_of_abs_one _ (hr 0)) (ne_zero_of_abs_one _ (hc 0))]
  exact lastMagnitude_signedMatrix (Rho5.Pivot.fixedSchur A)
    (fun i => row i.succ) (fun j => col j.succ)
    (fun i => hr i.succ) (fun j => hc j.succ)

theorem signedMatrix_fixed_order (A : Matrix3) (hA : FixedOrderNormalized3 A)
    (row col : Fin 3 → ℝ)
    (hr : ∀ i, |row i| = 1) (hc : ∀ j, |col j| = 1) :
    FixedOrderNormalized3 (signedMatrix A row col) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [signedMatrix_abs A row col hr hc i j]
    exact hA.1 i j
  · rw [signedMatrix_abs A row col hr hc 0 0]
    exact hA.2.1
  · rw [fixedSchur_signedMatrix A row col (first_pivot_ne_zero A hA)
      (ne_zero_of_abs_one _ (hr 0)) (ne_zero_of_abs_one _ (hc 0))]
    exact (signedMatrix_complete_iff (Rho5.Pivot.fixedSchur A)
      (fun i => row i.succ) (fun j => col j.succ)
      (fun i => hr i.succ) (fun j => hc j.succ) 0 0).2 hA.2.2

noncomputable def headRowSign (A : Matrix3) (i : Fin 3) : ℝ :=
  unitSign (A i 0)

noncomputable def headColSign (A : Matrix3) (j : Fin 3) : ℝ :=
  unitSign (A 0 0) * unitSign (A 0 j)

noncomputable def normalizeHead (A : Matrix3) : Matrix3 :=
  signedMatrix A (headRowSign A) (headColSign A)

theorem headRowSign_abs (A : Matrix3) (i : Fin 3) : |headRowSign A i| = 1 :=
  unitSign_abs _

theorem headColSign_abs (A : Matrix3) (j : Fin 3) : |headColSign A j| = 1 := by
  simp [headColSign, abs_mul, unitSign_abs]

theorem normalizeHead_abs (A : Matrix3) (i j : Fin 3) :
    |normalizeHead A i j| = |A i j| :=
  signedMatrix_abs A (headRowSign A) (headColSign A)
    (headRowSign_abs A) (headColSign_abs A) i j

theorem normalizeHead_first_column (A : Matrix3) (i : Fin 3) :
    normalizeHead A i 0 = |A i 0| := by
  change unitSign (A i 0) * A i 0 * (unitSign (A 0 0) * unitSign (A 0 0)) = _
  rw [unitSign_mul_self, mul_one, unitSign_mul]

theorem normalizeHead_first_row (A : Matrix3) (j : Fin 3) :
    normalizeHead A 0 j = |A 0 j| := by
  change unitSign (A 0 0) * A 0 j * (unitSign (A 0 0) * unitSign (A 0 j)) = _
  calc
    unitSign (A 0 0) * A 0 j * (unitSign (A 0 0) * unitSign (A 0 j)) =
        (unitSign (A 0 0) * unitSign (A 0 0)) * (unitSign (A 0 j) * A 0 j) := by ring
    _ = |A 0 j| := by rw [unitSign_mul_self, one_mul, unitSign_mul]

theorem normalizeHead_fixed_order (A : Matrix3) (hA : FixedOrderNormalized3 A) :
    FixedOrderNormalized3 (normalizeHead A) :=
  signedMatrix_fixed_order A hA (headRowSign A) (headColSign A)
    (headRowSign_abs A) (headColSign_abs A)

theorem normalizeHead_pivot (A : Matrix3) (hA : FixedOrderNormalized3 A) :
    normalizeHead A 0 0 = 1 :=
  (normalizeHead_first_column A 0).trans hA.2.1

theorem normalizeHead_secondMagnitude (A : Matrix3) (hA : FixedOrderNormalized3 A) :
    secondMagnitude (normalizeHead A) = secondMagnitude A :=
  secondMagnitude_signedMatrix A (headRowSign A) (headColSign A)
    (first_pivot_ne_zero A hA) (headRowSign_abs A) (headColSign_abs A)

theorem normalizeHead_thirdMagnitude (A : Matrix3) (hA : FixedOrderNormalized3 A) :
    thirdMagnitude (normalizeHead A) = thirdMagnitude A :=
  thirdMagnitude_signedMatrix A (headRowSign A) (headColSign A)
    (first_pivot_ne_zero A hA) (headRowSign_abs A) (headColSign_abs A)

end Rho5.ExternalThreePivot
