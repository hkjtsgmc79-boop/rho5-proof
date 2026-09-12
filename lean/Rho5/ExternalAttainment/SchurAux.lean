import Rho5.ExternalAttainment.Denominators
import Mathlib.Tactic.FinCases

/-!
Auxiliary module for the three same-matrix Schur identities `A → F → G → H`.

Stable recipe used for every entry of every one of the three identities:

`ext i j; fin_cases i <;> fin_cases j <;> simp [<both presentations>] <;>`
`try field_simp [<guards>] <;> ring`

* `simp` unfolds both presentations and reduces the `!![...]` literals, so entries that
  are already polynomial identities are closed by `ring` alone;
* the remaining entries differ only by cancellable factors such as `y * y⁻¹`; those need
  `field_simp` with the box's nonvanishing guards, hence `try` (a denominator-free goal
  makes `field_simp` fail, which is harmless);
* the guard set is fixed once and reused: the named forms `y_ne`, `x_add_one_ne`,
  `pivotTwo_pos`, `denomT_ne`, `denomR_ne`, `corePivot_ne`, plus the unfolded forms of
  `1+x`, `1+z`, `corePivot`, `denomT`, `denomR` (both in the definitional shape and in
  the `ring`-normalised shape that `field_simp` leaves in the goal), because
  `field_simp` matches denominators syntactically.

The card's handoff file `Rho5/ExternalAttainment/SchurIdentities.lean` keeps its twelve
declarations and delegates these three proofs here.
-/

noncomputable section
namespace Rho5.ExternalAttainment

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

variable {x y z g : ℝ}

/-- `A → F`: the first Schur tail of the actual candidate matrix. -/
theorem schur_matrixA_aux (box : Rho5.Algebraic.CandidateBox x y z g) :
    Rho5.Pivot.fixedSchur (matrixA x y z) = matrixF x y z := by
  have hx1 : (1 : ℝ) + x ≠ 0 := by simpa only [add_comm] using x_add_one_ne box
  have hz1 : (1 : ℝ) + z ≠ 0 := ne_of_gt (pivotTwo_pos box)
  have hc : 2 - x * z - z ^ 2 ≠ 0 := by simpa only [corePivot] using corePivot_ne box
  have hd : 2 * x ^ 2 * z + x * z ^ 2 + x * z - 2 * x - 2 ≠ 0 := by
    simpa only [denomT] using denomT_ne box
  have hr : 2 * x ^ 2 * z + x * z ^ 2 + x * z - 2 * x - 2 +
      z * (2 * x + z + 1) * (y + 1) ≠ 0 := by
    simpa only [denomR, denomT] using denomR_ne box
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rho5.Pivot.fixedSchur, matrixA, matrixF,
      reducedT, reducedB23, reducedB33, pivotTwo, headEntry, ratioRD,
      corePivot, topRight, denomR, denomT] <;>
    try field_simp [y_ne box, x_add_one_ne box, ne_of_gt (pivotTwo_pos box),
      denomT_ne box, denomR_ne box, corePivot_ne box, hx1, hz1, hc, hd, hr] <;>
    (try simp only [denomT, denomR, pivotTwo, corePivot]) <;>
    ring

/-- `F → G`: the second Schur tail (an identity on the whole box, no root equation). -/
theorem schur_matrixF_aux (box : Rho5.Algebraic.CandidateBox x y z g) :
    Rho5.Pivot.fixedSchur (matrixF x y z) = matrixG x y z := by
  have hx1 : (1 : ℝ) + x ≠ 0 := by simpa only [add_comm] using x_add_one_ne box
  have hz1 : (1 : ℝ) + z ≠ 0 := ne_of_gt (pivotTwo_pos box)
  have hc : 2 - x * z - z ^ 2 ≠ 0 := by simpa only [corePivot] using corePivot_ne box
  have hd : 2 * x ^ 2 * z + x * z ^ 2 + x * z - 2 * x - 2 ≠ 0 := by
    simpa only [denomT] using denomT_ne box
  have hr : 2 * x ^ 2 * z + x * z ^ 2 + x * z - 2 * x - 2 +
      z * (2 * x + z + 1) * (y + 1) ≠ 0 := by
    simpa only [denomR, denomT] using denomR_ne box
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rho5.Pivot.fixedSchur, matrixF, matrixG, pivotTwo,
      headEntry, ratioRD, corePivot, topRight, halfHeight,
      coreArm, coreBottom, coreCorner] <;>
    try field_simp [y_ne box, x_add_one_ne box, ne_of_gt (pivotTwo_pos box),
      denomT_ne box, denomR_ne box, corePivot_ne box, hx1, hz1, hc, hd, hr] <;>
    (try simp only [denomT, denomR, pivotTwo, corePivot]) <;>
    ring

/-- `G → H`: the third Schur tail; the pivot here is the actual `corePivot`. -/
theorem schur_matrixG_aux (box : Rho5.Algebraic.CandidateBox x y z g) :
    Rho5.Pivot.fixedSchur (matrixG x y z) = matrixH x y z := by
  have hx1 : (1 : ℝ) + x ≠ 0 := by simpa only [add_comm] using x_add_one_ne box
  have hz1 : (1 : ℝ) + z ≠ 0 := ne_of_gt (pivotTwo_pos box)
  have hc : 2 - x * z - z ^ 2 ≠ 0 := by simpa only [corePivot] using corePivot_ne box
  have hd : 2 * x ^ 2 * z + x * z ^ 2 + x * z - 2 * x - 2 ≠ 0 := by
    simpa only [denomT] using denomT_ne box
  have hr : 2 * x ^ 2 * z + x * z ^ 2 + x * z - 2 * x - 2 +
      z * (2 * x + z + 1) * (y + 1) ≠ 0 := by
    simpa only [denomR, denomT] using denomR_ne box
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rho5.Pivot.fixedSchur, matrixG, matrixH, coreArm, coreBottom,
      coreCorner, halfHeight] <;>
    try field_simp [y_ne box, x_add_one_ne box, ne_of_gt (pivotTwo_pos box),
      denomT_ne box, denomR_ne box, corePivot_ne box, hx1, hz1, hc, hd, hr] <;>
    (try simp only [denomT, denomR, pivotTwo, corePivot]) <;>
    ring

end Rho5.ExternalAttainment
