/-
D54 — the actual leading `3 × 3` block, the identity `det (B3 M) = p M * k M`, and the
resulting necessary constraint `p M * k M ≤ 4` on the normalized matrix.

`B3 M` is the leading `3 × 3` principal submatrix of the actual `5 × 5` matrix `M`
(the same restriction pattern D49 fixed for the leading `4 × 4` block: only a
`Fin.castSucc` embedding, no general submatrix framework).

The determinant identity is proved with the **signed** Schur determinant identity of
D27 (`det_eq_pivot_mul_det_fixedSchur`) applied twice: once to `B3 M` at `(0,0)`,
where the normalization `M 0 0 = 1` makes the pivot legal, and once to the resulting
`2 × 2` block, where `p M = S4 M 0 0 ≠ 0` is the legal pivot.  The `1 × 1` complement
is `S3 M 0 0 = k M` by D37's entry formula.  `k M` itself need not be nonzero — only
the two pivots that are actually divided by are required, and both appear explicitly
in the hypotheses.

Consequently, on a matrix with `matrixEntryMax M = 1` (so every entry is in the unit
cube) the item-1 bound applies to `B3 M`, giving `p M * k M ≤ 4` — a concrete
necessary constraint on the original normalized matrix and its first two pivots.
-/
import Rho5.Shared.MinorThreeBound.Vertex
import Rho5.Shared.TraceDeterminant
import Rho5.Shared.MatrixNormalization
import Rho5.Certificate.B24Extraction.Extract

namespace Rho5.MinorThreeBound

open Matrix
open Rho5 (matrixEntryMax)
open Rho5.MatrixNormalization (abs_entry_le_matrixEntryMax)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k S4_apply S3_apply)

/-! ## 1. The actual leading `3 × 3` block -/

/-- **The leading `3 × 3` block of the actual `5 × 5` matrix.**  Only a fixed
`Fin.castSucc` restriction: no embedding theory, no arbitrary submatrices. -/
noncomputable def B3 (M : Matrix5) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => M i.castSucc.castSucc j.castSucc.castSucc

/-- The corner entry of `B3` is the corner entry of `M`. -/
theorem B3_zero_zero (M : Matrix5) : B3 M 0 0 = M 0 0 := rfl

/-- Every entry of `B3 M` is an entry of `M`, so the cube condition transfers. -/
theorem abs_B3_entry_le (M : Matrix5) (i j : Fin 3) :
    |B3 M i j| ≤ matrixEntryMax M :=
  abs_entry_le_matrixEntryMax M _ _

/-! ## 2. Item 2 — `det (B3 M) = p M * k M` -/

/-- The top-left `2 × 2` of the first Schur update `S4 M`, as a `2 × 2` matrix. -/
noncomputable def B2 (M : Matrix5) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => S4 M i.castSucc.castSucc j.castSucc.castSucc

/-- The first Schur step of `B3 M` is exactly `B2 M`: both are
`M (i+1) (j+1) - M (i+1) 0 * M 0 (j+1) / M 0 0`. -/
theorem fixedSchur_B3 (M : Matrix5) :
    Rho5.Pivot.fixedSchur (B3 M) = B2 M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rho5.Pivot.fixedSchur, B3, B2, S4_apply]

/-- The `(0,0)` entry of `B2 M` is the pivot `p M`. -/
theorem B2_zero_zero (M : Matrix5) : B2 M 0 0 = p M := by
  simp [B2, p]

/-- The second Schur step of `B2 M` is the `1 × 1` matrix with entry `k M`: the
`2 × 2` complement `S4 M 1 1 - S4 M 1 0 * S4 M 0 1 / S4 M 0 0` is exactly the `(0,0)`
entry of the second update `S3 M`. -/
theorem fixedSchur_B2 (M : Matrix5) :
    Rho5.Pivot.fixedSchur (B2 M) = fun _ _ : Fin 1 => k M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rho5.Pivot.fixedSchur, B2, S3_apply, k]

/-- **Item 2.**  With `M 0 0 = 1` and `p M ≠ 0`, the determinant of the actual leading
`3 × 3` block is the product of the first two pivots.  Only the two pivots that are
divided by are assumed nonzero; `k M` is unrestricted. -/
theorem det_B3_eq (M : Matrix5) (h00 : M 0 0 = 1) (hp : p M ≠ 0) :
    (B3 M).det = p M * k M := by
  have hB00 : (B3 M) 0 0 ≠ 0 := by rw [B3_zero_zero, h00]; norm_num
  have h1 := Rho5.TraceDeterminant.det_eq_pivot_mul_det_fixedSchur (B3 M) hB00
  rw [fixedSchur_B3, B3_zero_zero, h00, one_mul] at h1
  have hB200 : B2 M 0 0 ≠ 0 := by rw [B2_zero_zero]; exact hp
  have h2 := Rho5.TraceDeterminant.det_eq_pivot_mul_det_fixedSchur (B2 M) hB200
  rw [fixedSchur_B2, Matrix.det_fin_one] at h2
  rw [h1, h2, B2_zero_zero]

/-! ## 3. Item 3 — the actual constraint `p M * k M ≤ 4` -/

/-- **Item 3 (absolute form).**  On a matrix whose entries are all in the unit cube,
the leading `3 × 3` determinant is bounded by the sharp constant `4`. -/
theorem abs_det_B3_le_four (M : Matrix5) (hmax : matrixEntryMax M = 1) :
    |(B3 M).det| ≤ 4 := by
  refine abs_det_le_four (B3 M) ?_
  intro i j
  have h := abs_B3_entry_le M i j
  rwa [hmax] at h

/-- **Item 3.**  With `matrixEntryMax M = 1`, the normalization `M 0 0 = 1` and the
first two pivots positive, the product `p M * k M` is at most `4`.  Every premise of
item 2 is preserved; positivity of `p M` supplies its non-vanishing. -/
theorem p_mul_k_le_four (M : Matrix5) (hmax : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hp : 0 < p M) (hk : 0 < k M) : p M * k M ≤ 4 := by
  rw [← det_B3_eq M h00 (ne_of_gt hp)]
  exact (le_abs_self _).trans (abs_det_B3_le_four M hmax)

/-- **Item 3 (absolute-value form).**  The nonnegative form needs no positivity of
`k M`: `p M ≠ 0` alone identifies the determinant with `p M * k M`. -/
theorem abs_p_mul_k_le_four (M : Matrix5) (hmax : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hp : p M ≠ 0) : |p M * k M| ≤ 4 := by
  rw [← det_B3_eq M h00 hp]
  exact abs_det_B3_le_four M hmax

end Rho5.MinorThreeBound
