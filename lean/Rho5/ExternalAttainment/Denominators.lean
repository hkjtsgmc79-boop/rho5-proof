import Rho5.ExternalAttainment.IntervalData
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace Rho5.ExternalAttainment

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

variable {x y z g : ℝ}

theorem y_ne (box : Rho5.Algebraic.CandidateBox x y z g) : y ≠ 0 := by
  have h := (narrowBox_of_candidateBox box).yb
  exact ne_of_lt (by linarith [h.2])

theorem x_add_one_pos (box : Rho5.Algebraic.CandidateBox x y z g) : 0 < x+1 := by
  have h := (narrowBox_of_candidateBox box).xb
  linarith [h.1]

theorem x_add_one_ne (box : Rho5.Algebraic.CandidateBox x y z g) : x+1 ≠ 0 :=
  ne_of_gt (x_add_one_pos box)

theorem denomT_ne (box : Rho5.Algebraic.CandidateBox x y z g) : denomT x y z ≠ 0 := by
  have h := (numerics_of_candidateBox box).denomT_bound
  exact ne_of_lt (by linarith [h.2])

theorem denomR_ne (box : Rho5.Algebraic.CandidateBox x y z g) : denomR x y z ≠ 0 := by
  have h := (numerics_of_candidateBox box).denomR_bound
  exact ne_of_lt (by linarith [h.2])

theorem pivotTwo_pos (box : Rho5.Algebraic.CandidateBox x y z g) : 0 < pivotTwo x y z := by
  have h := (numerics_of_candidateBox box).pivotTwo_bound
  linarith [h.1]

theorem corePivot_pos (box : Rho5.Algebraic.CandidateBox x y z g) : 0 < corePivot x y z := by
  have h := (numerics_of_candidateBox box).corePivot_bound
  linarith [h.1]

theorem corePivot_ne (box : Rho5.Algebraic.CandidateBox x y z g) : corePivot x y z ≠ 0 :=
  ne_of_gt (corePivot_pos box)

theorem halfHeight_pos (box : Rho5.Algebraic.CandidateBox x y z g) : 0 < halfHeight x y z := by
  have h := (numerics_of_candidateBox box).halfHeight_bound
  linarith [h.1]

/-- The full paper numerator reduces to the compact T used for interval bounds. -/
theorem paperT_eq (box : Rho5.Algebraic.CandidateBox x y z g) :
    paperT x y z = reducedT x y z := by
  dsimp only [paperT, reducedT, ratioRD]
  field_simp [denomT_ne box] <;>
    simp only [numerT, pivotTwo, denomR, denomT] <;> ring

theorem y_sub_paperT_ne (box : Rho5.Algebraic.CandidateBox x y z g) :
    y - paperT x y z ≠ 0 := by
  rw [paperT_eq box]
  have h := (numerics_of_candidateBox box).yMinusT_bound
  change Bounds _ _ (y - reducedT x y z) at h
  exact ne_of_lt (by linarith [h.2])

theorem reconstruction_product_ne (box : Rho5.Algebraic.CandidateBox x y z g) :
    y * (y - paperT x y z) ≠ 0 :=
  mul_ne_zero (y_ne box) (y_sub_paperT_ne box)

/-- No total-division shortcut is used: first cancel the actual nonzero
reconstruction denominator, then verify the polynomial identity. -/
theorem paperB23_eq (box : Rho5.Algebraic.CandidateBox x y z g) :
    paperB23 x y z = reducedB23 x y z := by
  dsimp only [paperB23]
  apply (div_eq_iff (reconstruction_product_ne box)).mpr
  simp only [paperT_eq box]
  dsimp only [reducedB23, reducedT, ratioRD, headEntry]
  field_simp [y_ne box, denomT_ne box, denomR_ne box] <;>
    simp only [pivotTwo, corePivot, denomR, denomT] <;> ring

theorem paperB33_eq (box : Rho5.Algebraic.CandidateBox x y z g) :
    paperB33 x y z = reducedB33 x y z := by
  dsimp only [paperB33]
  apply (div_eq_iff (reconstruction_product_ne box)).mpr
  simp only [paperT_eq box]
  dsimp only [reducedB33, reducedT, ratioRD, headEntry]
  field_simp [y_ne box, denomT_ne box, denomR_ne box] <;>
    simp only [pivotTwo, corePivot, denomR, denomT] <;> ring

end Rho5.ExternalAttainment
