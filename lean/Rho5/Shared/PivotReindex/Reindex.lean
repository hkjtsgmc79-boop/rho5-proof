/-
D10 / N03b — row/column reindexing of a real matrix
===================================================

Scope (frozen by the D10 task card).  This module supplies exactly the
*permutation* layer needed before a pivot can be moved to the active corner:

* `reindexEntries A eRow eCol` — the matrix whose `(i, j)` entry is `A (eRow i) (eCol j)`;
* inverse laws (reindexing twice with the inverse permutations restores `A`);
* commutation with scalar multiplication;
* the complete-pivot transport
  `IsCompletePivot (reindexEntries A eRow eCol) p q ↔ IsCompletePivot A (eRow p) (eCol q)`;
* for `Matrix5`: invariance of the frozen `matrixEntryMax`, and commutation with the
  D08 `normalize`.

Reused unchanged (read-only inputs, hashes checked in `results/INPUT_RECEIPT.json`):
* `Rho5.Matrix5`, `Rho5.matrixEntryMax` (`Rho5.Shared.Conventions`) — the maximum of
  the 25 entrywise absolute values; no second norm is introduced here;
* `Rho5.Pivot.IsCompletePivot` (`Rho5.Shared.Pivot`) — the frozen complete-pivot
  semantics with ties permitted; no second pivot predicate is introduced here;
* `Rho5.MatrixNormalization.{smul_apply_entry, normalize, normalize_eq_inv_smul}`
  (`Rho5.Shared.MatrixNormalization`, D08) — the entrywise reading of `smul` and the
  unit normalization.

No `sorry`, no new axiom, no `native_decide`.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixNormalization

namespace Rho5.PivotReindex

open Rho5

/-! ## The reindexed matrix -/

/-- **Item 1 (definition).** Row/column reindexing: the `(i, j)` entry of
`reindexEntries A eRow eCol` is the `(eRow i, eCol j)` entry of `A`.

This is the only permutation operation used by this lane.  It is *not* a new
matrix type and it does not change the norm or the pivot predicate: those are the
frozen `Rho5.matrixEntryMax` and `Rho5.Pivot.IsCompletePivot`. -/
def reindexEntries {ι κ : Type*} (A : Matrix ι κ ℝ) (eRow : ι ≃ ι) (eCol : κ ≃ κ) :
    Matrix ι κ ℝ :=
  fun i j => A (eRow i) (eCol j)

/-- Defining equation, kept for rewriting. -/
theorem reindexEntries_apply {ι κ : Type*} (A : Matrix ι κ ℝ) (eRow : ι ≃ ι)
    (eCol : κ ≃ κ) (i : ι) (j : κ) :
    reindexEntries A eRow eCol i j = A (eRow i) (eCol j) := rfl

/-- **Item 1 (inverse law).** Reindexing by `eRow`, `eCol` and then by the inverse
permutations restores the original matrix exactly. -/
theorem reindexEntries_reindex_symm {ι κ : Type*} (A : Matrix ι κ ℝ) (eRow : ι ≃ ι)
    (eCol : κ ≃ κ) :
    reindexEntries (reindexEntries A eRow eCol) eRow.symm eCol.symm = A := by
  funext i j
  simp only [reindexEntries, Equiv.apply_symm_apply]

/-- **Item 1 (inverse law, other orientation).** Reindexing by the inverse
permutations and then by `eRow`, `eCol` restores the original matrix.  Together
with the previous theorem this says the reindexing operation is a bijection on
matrices with inverse reindexing. -/
theorem reindexEntries_symm_reindex {ι κ : Type*} (A : Matrix ι κ ℝ) (eRow : ι ≃ ι)
    (eCol : κ ≃ κ) :
    reindexEntries (reindexEntries A eRow.symm eCol.symm) eRow eCol = A := by
  have h := reindexEntries_reindex_symm A eRow.symm eCol.symm
  simpa using h

/-- **Item 1 (scalar multiplication).** Reindexing commutes with scalar
multiplication.  The entrywise reading of `smul` is D08's
`Rho5.MatrixNormalization.smul_apply_entry`, not a re-derived one. -/
theorem reindexEntries_smul {ι κ : Type*} (c : ℝ) (A : Matrix ι κ ℝ) (eRow : ι ≃ ι)
    (eCol : κ ≃ κ) :
    reindexEntries (c • A) eRow eCol = c • reindexEntries A eRow eCol := by
  funext i j
  simp only [reindexEntries, Rho5.MatrixNormalization.smul_apply_entry]

/-- Reindexing is additive. -/
theorem reindexEntries_add {ι κ : Type*} (A B : Matrix ι κ ℝ) (eRow : ι ≃ ι)
    (eCol : κ ≃ κ) :
    reindexEntries (A + B) eRow eCol = reindexEntries A eRow eCol + reindexEntries B eRow eCol := by
  funext i j
  simp only [reindexEntries, Matrix.add_apply]

/-- Reindexing the zero matrix gives the zero matrix. -/
theorem reindexEntries_zero {ι κ : Type*} (eRow : ι ≃ ι) (eCol : κ ≃ κ) :
    reindexEntries (0 : Matrix ι κ ℝ) eRow eCol = 0 := by
  funext i j
  simp only [reindexEntries, Matrix.zero_apply]

/-- Reindexing is injective, i.e. it loses no information. -/
theorem reindexEntries_injective {ι κ : Type*} (eRow : ι ≃ ι) (eCol : κ ≃ κ) :
    Function.Injective (fun A : Matrix ι κ ℝ => reindexEntries A eRow eCol) := by
  intro A B h
  have h' := congrArg (fun C : Matrix ι κ ℝ => reindexEntries C eRow.symm eCol.symm) h
  simpa only [reindexEntries_reindex_symm] using h'

/-! ## Complete pivots are transported, not redefined -/

/-- **Item 1 (pivot transport).** A position `(p, q)` is a complete pivot of the
reindexed matrix exactly when the corresponding *original* position
`(eRow p, eCol q)` is a complete pivot of `A`.

The predicate is the frozen `Rho5.Pivot.IsCompletePivot`; the proof only uses
that `eRow` and `eCol` are bijections, so every tied maximizer is transported as
well (no uniqueness of the maximizer is used or implied). -/
theorem isCompletePivot_reindexEntries_iff {ι κ : Type*} (A : Matrix ι κ ℝ)
    (eRow : ι ≃ ι) (eCol : κ ≃ κ) (p : ι) (q : κ) :
    Rho5.Pivot.IsCompletePivot (reindexEntries A eRow eCol) p q ↔
      Rho5.Pivot.IsCompletePivot A (eRow p) (eCol q) := by
  constructor
  · intro h i j
    have h' := h (eRow.symm i) (eCol.symm j)
    simpa only [reindexEntries, Equiv.apply_symm_apply] using h'
  · intro h i j
    exact h (eRow i) (eCol j)

/-- The transport law with the permutations on the other side: the original
position `(p, q)` is a complete pivot of `A` exactly when the corresponding moved
position `(eRow p, eCol q)` is one of the inversely reindexed matrix.

This is the main transport law instantiated at `eRow.symm`, `eCol.symm`.  It is
recorded separately because the later stages read a *moved* position off a matrix
that already carries the permutation. -/
theorem isCompletePivot_reindexEntries_symm_iff {ι κ : Type*} (A : Matrix ι κ ℝ)
    (eRow : ι ≃ ι) (eCol : κ ≃ κ) (p : ι) (q : κ) :
    Rho5.Pivot.IsCompletePivot (reindexEntries A eRow.symm eCol.symm) (eRow p) (eCol q) ↔
      Rho5.Pivot.IsCompletePivot A p q := by
  rw [isCompletePivot_reindexEntries_iff]
  simp only [Equiv.symm_apply_apply]

/-- A tied maximizer stays a legal pivot after reindexing (transported
`Rho5.Pivot.tied_pivot`; ties are preserved, not broken). -/
theorem isCompletePivot_reindexEntries_tied {ι κ : Type*} (A : Matrix ι κ ℝ)
    (eRow : ι ≃ ι) (eCol : κ ≃ κ) (p p' : ι) (q q' : κ)
    (hmax : Rho5.Pivot.IsCompletePivot A p q) (htie : |A p' q'| = |A p q|) :
    Rho5.Pivot.IsCompletePivot (reindexEntries A eRow eCol) (eRow.symm p') (eCol.symm q') := by
  rw [isCompletePivot_reindexEntries_iff]
  simpa only [Equiv.apply_symm_apply] using
    Rho5.Pivot.tied_pivot A p p' q q' hmax htie

/-! ## The frozen entry maximum is permutation invariant (`Matrix5`) -/

/-- **Item 1 (`matrixEntryMax`).** For a `5 × 5` real matrix, reindexing rows and
columns does not change the frozen entry maximum `Rho5.matrixEntryMax`.  This is
where the *maximum* (not a mere bound) is used: both directions compare the two
suprema entry by entry. -/
theorem matrixEntryMax_reindexEntries (A : Matrix5) (eRow eCol : Fin 5 ≃ Fin 5) :
    matrixEntryMax (reindexEntries A eRow eCol) = matrixEntryMax A := by
  unfold matrixEntryMax
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le Finset.univ_nonempty _ (fun ij _ => ?_)
    exact Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax A (eRow ij.1) (eCol ij.2)
  · refine Finset.sup'_le Finset.univ_nonempty _ (fun ij _ => ?_)
    have h := Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax
      (reindexEntries A eRow eCol) (eRow.symm ij.1) (eCol.symm ij.2)
    simpa only [reindexEntries, Equiv.apply_symm_apply] using h

/-- The entrywise bound form: every reindexed entry is bounded by the *original*
entry maximum. -/
theorem abs_reindexEntries_le_matrixEntryMax (A : Matrix5) (eRow eCol : Fin 5 ≃ Fin 5)
    (i j : Fin 5) :
    |reindexEntries A eRow eCol i j| ≤ matrixEntryMax A := by
  rw [← matrixEntryMax_reindexEntries]
  exact Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax _ i j

/-- Reindexing preserves nonzeroness of a `Matrix5`. -/
theorem reindexEntries_ne_zero_iff (A : Matrix5) (eRow eCol : Fin 5 ≃ Fin 5) :
    reindexEntries A eRow eCol ≠ 0 ↔ A ≠ 0 := by
  constructor
  · intro h hA
    exact h (by rw [hA, reindexEntries_zero])
  · intro h hA
    refine h ?_
    have h' := congrArg (fun C : Matrix5 => reindexEntries C eRow.symm eCol.symm) hA
    simpa only [reindexEntries_reindex_symm, reindexEntries_zero] using h'

/-! ## Unit normalization commutes with reindexing -/

/-- **Item 1 (`normalize`).** D08's unit normalization commutes with row/column
reindexing.  No second normalization is defined: this is
`Rho5.MatrixNormalization.normalize` on both sides, and the proof uses the
permutation invariance of `matrixEntryMax` above. -/
theorem normalize_reindexEntries (A : Matrix5) (eRow eCol : Fin 5 ≃ Fin 5) :
    Rho5.MatrixNormalization.normalize (reindexEntries A eRow eCol) =
      reindexEntries (Rho5.MatrixNormalization.normalize A) eRow eCol := by
  simp only [Rho5.MatrixNormalization.normalize_eq_inv_smul, matrixEntryMax_reindexEntries,
    reindexEntries_smul]

/-- The same statement oriented as "reindexing the normalized matrix". -/
theorem reindexEntries_normalize (A : Matrix5) (eRow eCol : Fin 5 ≃ Fin 5) :
    reindexEntries (Rho5.MatrixNormalization.normalize A) eRow eCol =
      Rho5.MatrixNormalization.normalize (reindexEntries A eRow eCol) :=
  (normalize_reindexEntries A eRow eCol).symm

end Rho5.PivotReindex
