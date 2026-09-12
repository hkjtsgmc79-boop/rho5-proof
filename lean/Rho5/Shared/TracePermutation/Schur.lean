/-
D20 — the one-step Schur update commutes with row/column permutation
===================================================================

**Item 2, second half.** The pivot step of the permuted matrix is the permuted pivot
step of the original matrix, *through the remaining bijection*:

  `pivotSchur (permuteEntries A r c) p q
      = permuteEntries (pivotSchur A (r p) (c q)) (remainingPerm r p) (remainingPerm c q)`.

The two matrices are **not** claimed equal under the fixed `Fin` numbering; only the
cross-index correspondence is asserted, exactly as the card requires.  The proof is
the entrywise D10 formula `Rho5.PivotReindex.pivotSchur_apply` on both sides plus
`remainingIndex_remainingPerm`.
-/
import Rho5.Shared.TracePermutation.Remaining
import Rho5.Shared.PivotReindex

namespace Rho5.TracePermutation

open Rho5

/-- **Item 2 (Schur correspondence).** One elimination step at the pivot `(p, q)` of
the permuted matrix corresponds, through the remaining row/column bijections, to the
step at the original pivot `(r p, c q)`. -/
theorem pivotSchur_permuteEntries {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (r c : Equiv.Perm (Fin (n + 1))) (p q : Fin (n + 1)) :
    Rho5.PivotReindex.pivotSchur (permuteEntries A r c) p q
      = permuteEntries (Rho5.PivotReindex.pivotSchur A (r p) (c q))
          (remainingPerm r p) (remainingPerm c q) := by
  funext i j
  simp only [permuteEntries]
  rw [Rho5.PivotReindex.pivotSchur_apply, Rho5.PivotReindex.pivotSchur_apply]
  simp only [permuteEntries, remainingIndex_remainingPerm]

/-- The correspondence read at corresponding pivot positions: the step of the
permuted matrix at the moved pivot `(r.symm p, c.symm q)` is the permuted step of `A`
at `(p, q)`. -/
theorem pivotSchur_permuteEntries_symm {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (r c : Equiv.Perm (Fin (n + 1))) (p q : Fin (n + 1)) :
    Rho5.PivotReindex.pivotSchur (permuteEntries A r c) (r.symm p) (c.symm q)
      = permuteEntries (Rho5.PivotReindex.pivotSchur A p q)
          (remainingPerm r (r.symm p)) (remainingPerm c (c.symm q)) := by
  have h := pivotSchur_permuteEntries A r c (r.symm p) (c.symm q)
  simpa only [Equiv.apply_symm_apply] using h

/-- The permuted step, entrywise, in the original indices: combining the
correspondence with the D10 formula. -/
theorem pivotSchur_permuteEntries_apply {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (r c : Equiv.Perm (Fin (n + 1)))
    (p q : Fin (n + 1)) (i j : Fin n) :
    Rho5.PivotReindex.pivotSchur (permuteEntries A r c) p q i j
      = Rho5.PivotReindex.pivotSchur A (r p) (c q) (remainingPerm r p i)
          (remainingPerm c q j) := by
  rw [pivotSchur_permuteEntries]
  rfl

end Rho5.TracePermutation
