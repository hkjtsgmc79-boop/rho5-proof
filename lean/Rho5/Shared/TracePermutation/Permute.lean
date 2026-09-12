/-
D20 — arbitrary row/column permutation of a matrix
==================================================

The card fixes the entry point

  `permuteEntries A r c i j = A (r i) (c j)`,  `r c : Equiv.Perm (Fin n)`,

i.e. exactly D10's `Rho5.PivotReindex.reindexEntries` (definitionally the same
function).  This file records the *correspondence* facts item 1 asks for and reuses
the D10 results instead of reproving one-step lemmas:

* inverse law, action on the zero matrix, nonzeroness (zero-matrix qualification);
* the absolute value correspondence `|permuteEntries A r c i j| = |A (r i) (c j)|`
  and the pivot-position correspondence
  `IsCompletePivot (permuteEntries A r c) (r.symm p) (c.symm q) ↔ IsCompletePivot A p q`
  with equal absolute pivot value;
* invariance of the entry maximum: the frozen 5×5 `Rho5.matrixEntryMax` (cited from
  D10) and, for every nonempty stage size, D12's `Rho5.MatrixStage.stageEntryMax`.

Nothing here assumes that the permuted matrix equals the original under the fixed
`Fin` numbering; only the *bijective* correspondence is used.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixStage
import Rho5.Shared.PivotReindex
import Rho5.Shared.CompletePivotPath

namespace Rho5.TracePermutation

open Rho5

/-- **Item 1 (fixed entry definition).** Row/column permutation of a real square
matrix: the `(i, j)` entry becomes the `(r i, c j)` entry. -/
def permuteEntries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r c : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A (r i) (c j)

/-- Bridge: `permuteEntries` *is* D10's `reindexEntries` (definitionally), so every
D10 reindexing result applies verbatim. -/
theorem permuteEntries_eq_reindexEntries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Equiv.Perm (Fin n)) :
    permuteEntries A r c = Rho5.PivotReindex.reindexEntries A r c := rfl

/-- Defining equation. -/
theorem permuteEntries_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r c : Equiv.Perm (Fin n))
    (i j : Fin n) : permuteEntries A r c i j = A (r i) (c j) := rfl

/-- **Item 1 (inverse).** Permuting by the inverse permutations restores the matrix
(D10's `reindexEntries_reindex_symm`). -/
theorem permuteEntries_permuteEntries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Equiv.Perm (Fin n)) :
    permuteEntries (permuteEntries A r c) r.symm c.symm = A :=
  Rho5.PivotReindex.reindexEntries_reindex_symm A r c

/-- The other orientation of the inverse law. -/
theorem permuteEntries_symm_permuteEntries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Equiv.Perm (Fin n)) :
    permuteEntries (permuteEntries A r c) r.symm c.symm = A :=
  permuteEntries_permuteEntries A r c

/-- Permuting the zero matrix gives the zero matrix (D10). -/
theorem permuteEntries_zero {n : ℕ} (r c : Equiv.Perm (Fin n)) :
    permuteEntries (0 : Matrix (Fin n) (Fin n) ℝ) r c = 0 :=
  Rho5.PivotReindex.reindexEntries_zero r c

/-- **Item 1 (zero-matrix qualification).** Permuting is a bijection on matrices, so
it preserves and reflects being the zero matrix: the zero stop of the permuted
matrix is exactly the zero stop of the original. -/
theorem permuteEntries_eq_zero_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Equiv.Perm (Fin n)) :
    permuteEntries A r c = 0 ↔ A = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => permuteEntries B r.symm c.symm) h
    simpa only [permuteEntries_permuteEntries, permuteEntries_zero] using h'
  · intro h
    rw [h, permuteEntries_zero]

/-- Permuting preserves nonzeroness (the form the `step` constructor consumes). -/
theorem permuteEntries_ne_zero_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Equiv.Perm (Fin n)) :
    permuteEntries A r c ≠ 0 ↔ A ≠ 0 :=
  not_congr (permuteEntries_eq_zero_iff A r c)

/-- **Item 1 (absolute value correspondence).** Entrywise, the absolute value of a
permuted entry is the absolute value of the corresponding original entry. -/
theorem abs_permuteEntries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r c : Equiv.Perm (Fin n))
    (i j : Fin n) : |permuteEntries A r c i j| = |A (r i) (c j)| := rfl

/-- **Item 1 (legal pivots correspond).** A position is a complete pivot of the
permuted matrix exactly when the corresponding original position is one of `A`
(D10's transport, ties included). -/
theorem isCompletePivot_permuteEntries_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Equiv.Perm (Fin n)) (p q : Fin n) :
    Rho5.Pivot.IsCompletePivot (permuteEntries A r c) p q ↔
      Rho5.Pivot.IsCompletePivot A (r p) (c q) :=
  Rho5.PivotReindex.isCompletePivot_reindexEntries_iff A r c p q

/-- **Item 1 (corresponding pivot position).** Reading the previous equivalence at
`(r.symm p, c.symm q)`: the permuted matrix has a complete pivot exactly at the
moved position when `A` has one at `(p, q)`. -/
theorem isCompletePivot_permuteEntries_symm_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Equiv.Perm (Fin n)) (p q : Fin n) :
    Rho5.Pivot.IsCompletePivot (permuteEntries A r c) (r.symm p) (c.symm q) ↔
      Rho5.Pivot.IsCompletePivot A p q := by
  rw [isCompletePivot_permuteEntries_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Item 1 (absolute pivot value).** At corresponding pivot positions the absolute
pivot values agree. -/
theorem abs_permuteEntries_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Equiv.Perm (Fin n)) (p q : Fin n) :
    |permuteEntries A r c (r.symm p) (c.symm q)| = |A p q| := by
  simp only [abs_permuteEntries, Equiv.apply_symm_apply]

/-- **Item 1 (entry maximum, every nonempty stage).** D12's `stageEntryMax` is
invariant under row/column permutation. -/
theorem stageEntryMax_permuteEntries {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (r c : Equiv.Perm (Fin (n + 1))) :
    Rho5.MatrixStage.stageEntryMax (permuteEntries A r c) = Rho5.MatrixStage.stageEntryMax A := by
  unfold Rho5.MatrixStage.stageEntryMax
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le Finset.univ_nonempty _ (fun ij _ => ?_)
    exact (Finset.le_sup'_iff Finset.univ_nonempty).mpr
      ⟨(r ij.1, c ij.2), Finset.mem_univ _, le_rfl⟩
  · refine Finset.sup'_le Finset.univ_nonempty _ (fun ij _ => ?_)
    refine (Finset.le_sup'_iff Finset.univ_nonempty).mpr
      ⟨(r.symm ij.1, c.symm ij.2), Finset.mem_univ _, ?_⟩
    simpa only [permuteEntries, Equiv.apply_symm_apply] using le_rfl

/-- **Item 1 (frozen 5×5 entry maximum).** D10's invariance result for
`Rho5.matrixEntryMax`, restated for `permuteEntries`. -/
theorem matrixEntryMax_permuteEntries (A : Matrix5) (r c : Equiv.Perm (Fin 5)) :
    matrixEntryMax (permuteEntries A r c) = matrixEntryMax A :=
  Rho5.PivotReindex.matrixEntryMax_reindexEntries A r c

end Rho5.TracePermutation
