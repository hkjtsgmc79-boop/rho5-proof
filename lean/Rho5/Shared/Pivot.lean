import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-! Local complete-pivot semantics. Ties are permitted. This module does not
yet implement the full five-stage path or its normalization equivalences. -/
namespace Rho5.Pivot

def IsCompletePivot {ι κ : Type*} (A : Matrix ι κ ℝ) (p : ι) (q : κ) : Prop :=
  ∀ i j, |A i j| ≤ |A p q|

theorem zero_complete_pivot {ι κ : Type*} (A : Matrix ι κ ℝ) (p : ι) (q : κ)
    (hmax : IsCompletePivot A p q) (hzero : A p q = 0) :
    ∀ i j, A i j = 0 := by
  intro i j
  apply abs_eq_zero.mp
  apply le_antisymm
  · simpa [hzero] using hmax i j
  · exact abs_nonneg _

/-- Any tied maximizer is legal; no arbitrary tie-break rule is built in. -/
theorem tied_pivot {ι κ : Type*} (A : Matrix ι κ ℝ) (p p' : ι) (q q' : κ)
    (hmax : IsCompletePivot A p q) (htie : |A p' q'| = |A p q|) :
    IsCompletePivot A p' q' := by
  intro i j
  rw [htie]
  exact hmax i j

/-- Fixed-order Schur update; the intended nonzero-pivot qualification remains
explicit in any theorem interpreting this total real expression. -/
noncomputable def fixedSchur {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0

#print axioms zero_complete_pivot
#print axioms tied_pivot
end Rho5.Pivot
