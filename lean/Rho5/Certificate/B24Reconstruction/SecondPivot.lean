import Rho5.Certificate.B24Reconstruction.Basic

/-!
# D28 / B24Reconstruction — the second real elimination step

**Item 2 of the card.**  One further frozen complete-pivot step with the pivot at the
active corner `(0, 0)` applied to the first stage `firstStage z` returns the frozen
`B16.D z` — the actual 3 × 3 core — under the single explicit hypothesis `p ≠ 0`.

Again this is the index-level computation: the `(i, j)` entry of the update is
`firstStage (i+1) (j+1) - firstStage (i+1) 0 * firstStage 0 (j+1) / firstStage 0 0`
`= (D_ij + x_i q_j) - (p x_i) q_j / p`, and `p ≠ 0` is exactly what removes the
denominator.  The hypothesis is kept explicit: `p = 0` would make the step
illegitimate (the pivot entry vanishes), and no sign or boundedness assumption is
smuggled in here.
-/

namespace Rho5.Certificate.B24Reconstruction

open Rho5.Certificate.B16 (Point D O S L P u xv v q Physical)

/-- **Item 2.**  Under `p ≠ 0`, the second complete-pivot step on the first stage is
the frozen `B16.D z`.  This is the real second elimination step of the model: the
`4 × 4` stage collapses to the actual `3 × 3` core `D`. -/
theorem pivotSchur_firstStage_zero_zero (z : Point) (hp : p z ≠ 0) :
    Rho5.PivotReindex.pivotSchur (firstStage z) 0 0 = D z := by
  funext i j
  rw [Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]
  simp only [Rho5.Pivot.fixedSchur]
  fin_cases i <;> fin_cases j <;>
    simp [firstStage, S, x_eq_xv] <;>
    field_simp [hp] <;> ring_nf

/-- Entrywise form of the second step. -/
theorem pivotSchur_firstStage_zero_zero_apply (z : Point) (hp : p z ≠ 0) (i j : Fin 3) :
    Rho5.PivotReindex.pivotSchur (firstStage z) 0 0 i j = D z i j :=
  congrFun (congrFun (pivotSchur_firstStage_zero_zero z hp) i) j

/-- The second step is available as soon as `p > 0`; the positivity form is what the
reference's head band provides. -/
theorem pivotSchur_firstStage_zero_zero_of_pos (z : Point) (hp : 0 < p z) :
    Rho5.PivotReindex.pivotSchur (firstStage z) 0 0 = D z :=
  pivotSchur_firstStage_zero_zero z (ne_of_gt hp)

end Rho5.Certificate.B24Reconstruction
