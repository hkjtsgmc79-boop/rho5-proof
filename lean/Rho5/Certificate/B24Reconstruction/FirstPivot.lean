import Rho5.Certificate.B24Reconstruction.Basic

/-!
# D28 / B24Reconstruction — the first real elimination step

**Item 1 of the card.**  One frozen complete-pivot step `Rho5.PivotReindex.pivotSchur`
with the pivot at the active corner `(0, 0)` applied to the reconstructed matrix
`reconstruct z` is exactly the reference's first stage `[[p, qᵀ], [px, D + xqᵀ]]`.

The proof is the *index-level* computation, not a string identity: with the pivot `0`
the remaining-index map is the successor (the frozen `pivotSchur` is
`fixedSchur` of the moved matrix, and moving `(0, 0)` is the identity), so the update
of entry `(i, j)` is
`M (i+1) (j+1) - M (i+1) 0 * M 0 (j+1) / M 0 0`
and each of the sixteen `(i, j)` pairs is closed by `ring` after the reconstruction
table has been unfolded.  The pivot entry is `M 0 0 = 1`, so no nonzero hypothesis
enters (division by `1` is not a division by zero).

The step is *legal* (complete pivot and nonzero pivot entry) under the explicit
head-band conditions; that is `PivotLegal`.
-/

namespace Rho5.Certificate.B24Reconstruction

open Rho5.Certificate.B16 (Point D O S L P u xv v q Physical)

/-- **Item 1.**  The first complete-pivot elimination step on the reconstructed
matrix is the reference's first stage, for every B24 point.  No hypothesis on `z` is
used. -/
theorem pivotSchur_reconstruct_zero_zero (z : Point) :
    Rho5.PivotReindex.pivotSchur (reconstruct z) 0 0 = firstStage z := by
  funext i j
  rw [Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]
  simp only [Rho5.Pivot.fixedSchur]
  fin_cases i <;> fin_cases j <;>
    simp [reconstruct, firstStage, P, O, S, beta, x_eq_xv] <;> ring_nf

/-- Entrywise form of the first step, kept for downstream rewriting. -/
theorem pivotSchur_reconstruct_zero_zero_apply (z : Point) (i j : Fin 4) :
    Rho5.PivotReindex.pivotSchur (reconstruct z) 0 0 i j = firstStage z i j :=
  congrFun (congrFun (pivotSchur_reconstruct_zero_zero z) i) j

end Rho5.Certificate.B24Reconstruction
