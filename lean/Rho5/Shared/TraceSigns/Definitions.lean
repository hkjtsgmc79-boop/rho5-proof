/-
D22 — row/column sign flips: sign vectors, signed matrices, entry-level invariance
==================================================================================

A *sign flip* multiplies row `i` by `r i` and column `j` by `c j`, where every
`r i` and every `c j` is `±1` (`IsSign`).  This module provides

* the sign-vector API (`IsSign` and its equivalent absolute-value form),
* the signed matrix `signedEntries A r c`,
* **Goal 1**: entry absolute values, the zero/non-zero qualification, the
  complete-pivot qualification and the pivot absolute value are all preserved.

Row and column **permutations** are a different transformation and belong to D20;
nothing here permutes an index.  The hypothesis is exactly `|r i| = 1`, not
arbitrary non-zero scaling.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixNormalization
import Rho5.Shared.PivotReindex
import Rho5.Shared.CompletePivotPath

namespace Rho5.TraceSigns

open Rho5

/-! ## 1. Sign vectors -/

/-- A row/column sign vector: every entry is `1` or `-1`. -/
def IsSign {ι : Type*} (r : ι → ℝ) : Prop := ∀ i, r i = 1 ∨ r i = -1

/-- The equivalent absolute-value form of the sign condition. -/
theorem isSign_iff_abs_eq_one {ι : Type*} (r : ι → ℝ) :
    IsSign r ↔ ∀ i, |r i| = 1 := by
  constructor
  · intro h i
    rcases h i with h' | h' <;> simp [h']
  · intro h i
    have h2 : r i * r i = 1 := by
      have h3 : |r i| * |r i| = 1 := by rw [h i]; norm_num
      rwa [abs_mul_abs_self] at h3
    rcases mul_self_eq_one_iff.mp h2 with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'

theorem IsSign.abs_eq_one {ι : Type*} {r : ι → ℝ} (h : IsSign r) (i : ι) : |r i| = 1 :=
  (isSign_iff_abs_eq_one r).mp h i

/-- Every sign squares to `1`. -/
theorem IsSign.mul_self {ι : Type*} {r : ι → ℝ} (h : IsSign r) (i : ι) : r i * r i = 1 := by
  rcases h i with h' | h' <;> rw [h'] <;> norm_num

/-- A sign is its own inverse. -/
theorem IsSign.inv_eq_self {ι : Type*} {r : ι → ℝ} (h : IsSign r) (i : ι) :
    (r i)⁻¹ = r i := by
  have h2 : r i * r i = 1 := h.mul_self i
  rw [inv_eq_of_mul_eq_one_right h2]

/-- A sign never vanishes. -/
theorem IsSign.ne_zero {ι : Type*} {r : ι → ℝ} (h : IsSign r) (i : ι) : r i ≠ 0 := by
  intro h0
  have h2 : r i * r i = 1 := h.mul_self i
  rw [h0, mul_zero] at h2
  exact zero_ne_one h2

/-- The pointwise inverse of a sign vector is again a sign vector. -/
theorem IsSign.inv {ι : Type*} {r : ι → ℝ} (h : IsSign r) : IsSign fun i => (r i)⁻¹ := by
  intro i
  change (r i)⁻¹ = 1 ∨ (r i)⁻¹ = -1
  rw [h.inv_eq_self i]
  exact h i

/-- The remaining-index restriction of a sign vector is a sign vector. -/
theorem IsSign.comp_remaining {n : ℕ} {r : Fin (n + 1) → ℝ} (hr : IsSign r)
    (p : Fin (n + 1)) : IsSign fun i => r (Rho5.PivotReindex.remainingIndex p i) :=
  fun i => hr _

/-! ## 2. Entries: absolute value, zero and pivot qualification -/

/-- **The signed matrix** `(i, j) ↦ r i * A i j * c j`: row `i` scaled by `r i`,
column `j` scaled by `c j`. -/
def signedEntries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r c : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => r i * A i j * c j

@[simp] theorem signedEntries_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Fin n → ℝ) (i j : Fin n) : signedEntries A r c i j = r i * A i j * c j := rfl

/-- Applying the same sign flip twice returns the original matrix. -/
theorem signedEntries_involutive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {r c : Fin n → ℝ} (hr : IsSign r) (hc : IsSign c) :
    signedEntries (signedEntries A r c) r c = A := by
  funext i j
  have hri : r i ^ 2 = 1 := by rw [pow_two]; exact hr.mul_self i
  have hcj : c j ^ 2 = 1 := by rw [pow_two]; exact hc.mul_self j
  simp only [signedEntries_apply]
  ring_nf
  linear_combination (A i j * c j ^ 2) * hri + (A i j) * hcj

/-- **Involution with the inverse signs.**  Applying `r⁻¹`, `c⁻¹` to an already
signed matrix returns the original matrix; this is the form the reverse direction
of Goal 3 uses. -/
theorem signedEntries_involutive_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {r c : Fin n → ℝ} (hr : IsSign r) (hc : IsSign c) :
    signedEntries (signedEntries A r c) (fun i => (r i)⁻¹) (fun j => (c j)⁻¹) = A := by
  funext i j
  have hpi : (r i)⁻¹ = r i := hr.inv_eq_self i
  have hpj : (c j)⁻¹ = c j := hc.inv_eq_self j
  have hri : r i ^ 2 = 1 := by rw [pow_two]; exact hr.mul_self i
  have hcj : c j ^ 2 = 1 := by rw [pow_two]; exact hc.mul_self j
  simp only [signedEntries_apply]
  rw [hpi, hpj]
  ring_nf
  linear_combination (A i j * c j ^ 2) * hri + (A i j) * hcj

/-- **Goal 1 (absolute values).**  A sign flip does not change any entry's
absolute value. -/
theorem abs_signedEntries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {r c : Fin n → ℝ} (hr : IsSign r) (hc : IsSign c) (i j : Fin n) :
    |signedEntries A r c i j| = |A i j| := by
  rw [signedEntries_apply, abs_mul, abs_mul, hr.abs_eq_one i, hc.abs_eq_one j]
  ring

/-- **Goal 1 (zero qualification).**  A sign flip does not change which entries
vanish. -/
theorem signedEntries_eq_zero_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {r c : Fin n → ℝ} (hr : IsSign r) (hc : IsSign c) (i j : Fin n) :
    signedEntries A r c i j = 0 ↔ A i j = 0 := by
  rw [signedEntries_apply, mul_eq_zero, mul_eq_zero]
  simp only [hr.ne_zero i, hc.ne_zero j, false_or, or_false]

/-- **Goal 1 (zero matrix).**  A signed matrix is the zero matrix exactly when the
original matrix is. -/
theorem signedEntries_eq_zero_iff' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {r c : Fin n → ℝ} (hr : IsSign r) (hc : IsSign c) :
    signedEntries A r c = 0 ↔ A = 0 := by
  constructor
  · intro h
    calc A = signedEntries (signedEntries A r c) r c := (signedEntries_involutive A hr hc).symm
      _ = signedEntries 0 r c := by rw [h]
      _ = 0 := by
        funext i j
        simp
  · intro h
    rw [h]
    funext i j
    simp

/-- **Goal 1 (complete-pivot qualification).**  `(p, q)` is a complete pivot of the
signed matrix exactly when it is one of the original matrix.  Ties are preserved,
because only absolute values are compared. -/
theorem isCompletePivot_signedEntries_iff {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) {r c : Fin (n + 1) → ℝ}
    (hr : IsSign r) (hc : IsSign c) (p q : Fin (n + 1)) :
    Rho5.Pivot.IsCompletePivot (signedEntries A r c) p q ↔
      Rho5.Pivot.IsCompletePivot A p q := by
  constructor
  · intro h i j
    have h' := h i j
    rwa [abs_signedEntries A hr hc i j, abs_signedEntries A hr hc p q] at h'
  · intro h i j
    rw [abs_signedEntries A hr hc i j, abs_signedEntries A hr hc p q]
    exact h i j

/-- **Goal 1 (pivot absolute value).**  The recorded pivot absolute value is
unchanged. -/
theorem abs_pivot_signedEntries {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {r c : Fin (n + 1) → ℝ} (hr : IsSign r) (hc : IsSign c) (p q : Fin (n + 1)) :
    |signedEntries A r c p q| = |A p q| :=
  abs_signedEntries A hr hc p q

end Rho5.TraceSigns
