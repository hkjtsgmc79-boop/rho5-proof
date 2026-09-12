import Rho5.Certificate.B24Reconstruction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# D33 / B24Trace — the last three elimination steps of the reconstructed matrix

D28 reconstructed the real `5 × 5` matrix `reconstruct z`
from the same B24 coordinates and proved the first two complete-pivot steps:

* `pivotSchur (reconstruct z) 0 0 = firstStage z`,
* `p z ≠ 0 → pivotSchur (firstStage z) 0 0 = D z`.

This file continues the honest index-level computation:

* **step 3** — `k ≠ 0 → pivotSchur (D z) 0 0 = [[r, s], [t, -r]]` with the *real*
  coordinates `k = z 0`, `r = z 1`, `s = z 2`, `t = z 3`;
* **step 4** — `r ≠ 0 → pivotSchur [[r, s], [t, -r]] 0 0` is the `1 × 1` matrix with
  entry `-(r + s t / r)`, connected to `-z 23` by the frozen `Physical.height`;
* **step 5** — the real `pivotSchur` of that `1 × 1` matrix is the `0 × 0` matrix,
  whose only legal trace is the empty one (no extra `0` is appended).

The two tail matrices below are the *actual* Schur tails of the D28 reconstruction
(they are proved equal to the corresponding `pivotSchur` outputs), not a new model:
`tail2` is `[[r, s], [t, -r]]` and `tail1` is the `1 × 1` block `[-(r + st/r)]`.
Nothing of D28 (`reconstruct`, `firstStage`, `HeadBand`, `Physical`, `D`, `S`, …) is
redefined or shadowed.
-/

namespace Rho5.Certificate.B24Trace

open Rho5.Certificate.B16 (Point D O S L P u xv v q Physical)
open Rho5.Certificate.B24Reconstruction (reconstruct firstStage p reconstruct_zero_zero
  firstStage_zero_zero)

/-! ## The actual tail matrices -/

/-- The real `2 × 2` tail after the third legal step: `[[r, s], [t, -r]]` in the
B24 coordinates `r = z 1`, `s = z 2`, `t = z 3`.  `pivotSchur_tail2` below proves
this is exactly what the frozen `pivotSchur` produces. -/
noncomputable def tail2 (z : Point) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![z 1, z 2], ![z 3, -z 1]]

/-- The real `1 × 1` tail after the fourth legal step, whose single entry is
`-(r + s t / r)`.  `Physical.height` identifies it with `-z 23`. -/
noncomputable def tail1 (z : Point) : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.of fun _ _ => -(z 1 + z 2 * z 3 / z 1)

/-! ## Step 3 — the `3 × 3` core `D` collapses to `[[r, s], [t, -r]]` -/

/-- **Item 1 (step 3).**  With `k = z 0 ≠ 0` the third complete-pivot step on the
frozen `B16.D z` is the real `2 × 2` tail `[[r, s], [t, -r]]`.  The two `c`- and
`d`-rows cancel exactly against the pivot row/column: `(r + cA) - (ck)A/k = r`,
`(s + cB) - (ck)B/k = s`, `(t + dA) - (dk)A/k = t`, `(-r + dB) - (dk)B/k = -r`. -/
theorem pivotSchur_D_zero_zero (z : Point) (hk : z 0 ≠ 0) :
    Rho5.PivotReindex.pivotSchur (D z) 0 0 = tail2 z := by
  funext i j
  rw [Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]
  simp only [Rho5.Pivot.fixedSchur]
  fin_cases i <;> fin_cases j <;>
    simp [D, tail2] <;> field_simp [hk] <;> ring

/-! ## Step 4 — the `2 × 2` tail collapses to the `1 × 1` entry `-(r + st/r)` -/

/-- **Item 1 (step 4).**  With `r = z 1 ≠ 0` the fourth complete-pivot step on
`[[r, s], [t, -r]]` is the `1 × 1` matrix with entry `-r - t s / r`, written in the
reference's shape `-(r + s t / r)`. -/
theorem pivotSchur_tail2_zero_zero (z : Point) (hr : z 1 ≠ 0) :
    Rho5.PivotReindex.pivotSchur (tail2 z) 0 0 = tail1 z := by
  funext i j
  rw [Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]
  simp only [Rho5.Pivot.fixedSchur]
  fin_cases i <;> fin_cases j <;>
    simp [tail2, tail1] <;> field_simp [hr] <;> ring

/-! ## Step 5 — the `1 × 1` tail is eliminated to the `0 × 0` matrix -/

/-- **Item 1 (step 5).**  The frozen `pivotSchur` of the `1 × 1` tail is the
`0 × 0` matrix (there is no entry left; the remaining index set is empty). -/
theorem pivotSchur_tail1_zero_zero (z : Point) :
    Rho5.PivotReindex.pivotSchur (tail1 z) 0 0 = 0 := by
  funext i j
  exact Fin.elim0 i

/-! ## Values of the pivots, as absolute values -/

theorem D_zero_zero (z : Point) : D z 0 0 = z 0 := rfl

theorem tail2_zero_zero (z : Point) : tail2 z 0 0 = z 1 := by simp [tail2]

theorem tail1_zero_zero (z : Point) : tail1 z 0 0 = -(z 1 + z 2 * z 3 / z 1) := by
  simp [tail1]

/-- The frozen `Physical.height` in the reference's coordinate names:
`F = r + s t / r`. -/
theorem height_rst (z : Point) (hz : Physical z) : z 1 + z 2 * z 3 / z 1 = z 23 :=
  hz.height.symm

/-- **Item 1 (height connection).**  The fourth-step entry is `-z 23`, i.e. minus the
real height coordinate. -/
theorem tail1_zero_zero_height (z : Point) (hz : Physical z) : tail1 z 0 0 = -z 23 := by
  rw [tail1_zero_zero, height_rst z hz]

/-- **Item 2 (`F > 0`).**  From `r > 0`, `0 ≤ s` and `0 ≤ t` the height coordinate
`F = z 23` is strictly positive.  (`Physical` supplies `r > 0`; `0 ≤ s`, `0 ≤ t` are
the extra explicit conditions of this card.) -/
theorem F_pos (z : Point) (hz : Physical z) (hs : 0 ≤ z 2) (ht : 0 ≤ z 3) :
    0 < z 23 := by
  rw [hz.height]
  have hr : 0 < z 1 := hz.r_pos
  have hst : 0 ≤ z 2 * z 3 / z 1 := div_nonneg (mul_nonneg hs ht) (le_of_lt hr)
  linarith

theorem abs_reconstruct_zero_zero (z : Point) : |reconstruct z 0 0| = 1 := by
  rw [reconstruct_zero_zero, abs_one]

theorem abs_firstStage_zero_zero (z : Point) (hp : 0 < p z) :
    |firstStage z 0 0| = p z := by
  rw [firstStage_zero_zero, abs_of_pos hp]

theorem abs_D_zero_zero (z : Point) (hk : 0 < z 0) : |D z 0 0| = z 0 := by
  rw [D_zero_zero, abs_of_nonneg (le_of_lt hk)]

theorem abs_tail2_zero_zero (z : Point) (hr : 0 < z 1) : |tail2 z 0 0| = z 1 := by
  rw [tail2_zero_zero, abs_of_pos hr]

/-- **Item 1 (height connection, absolute value).**  The fifth pivot value is
`F = z 23`. -/
theorem abs_tail1_zero_zero (z : Point) (hz : Physical z) (hF : 0 < z 23) :
    |tail1 z 0 0| = z 23 := by
  rw [tail1_zero_zero]
  have h : 0 ≤ z 1 + z 2 * z 3 / z 1 := by
    rw [height_rst z hz]
    exact le_of_lt hF
  rw [abs_neg, abs_of_nonneg h, height_rst z hz]

end Rho5.Certificate.B24Trace
