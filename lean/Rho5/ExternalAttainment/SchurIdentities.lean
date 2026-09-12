import Rho5.ExternalAttainment.SchurAux
import Mathlib.Tactic.FinCases

noncomputable section
namespace Rho5.ExternalAttainment

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

variable {x y z g : ℝ}

theorem candidate_eq_matrixA (box : Rho5.Algebraic.CandidateBox x y z g) :
    candidateMatrix x y z g = matrixA x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [candidateMatrix, matrixA, paperT_eq box, paperB23_eq box,
      paperB33_eq box, topRight] <;>
    field_simp [y_ne box] <;> ring

/-- The A → F identity carries the box's nonvanishing guards: `fixedSchur` and both
matrix presentations use totalized division by `y`, `x+1`, `denomT`, `denomR`.
(Repaired statement: the source asked for arbitrary `x y z`, which is false under
Lean's totalized division when a denominator vanishes.) -/
theorem schur_matrixA (box : Rho5.Algebraic.CandidateBox x y z g) :
    Rho5.Pivot.fixedSchur (matrixA x y z) = matrixF x y z := schur_matrixA_aux box

theorem schur_matrixF (box : Rho5.Algebraic.CandidateBox x y z g) :
    Rho5.Pivot.fixedSchur (matrixF x y z) = matrixG x y z := schur_matrixF_aux box

theorem schur_matrixG (box : Rho5.Algebraic.CandidateBox x y z g) :
    Rho5.Pivot.fixedSchur (matrixG x y z) = matrixH x y z := schur_matrixG_aux box

theorem stageF_eq (box : Rho5.Algebraic.CandidateBox x y z g) :
    stageF x y z g = matrixF x y z := by
  rw [stageF, candidate_eq_matrixA box, schur_matrixA box]

theorem stageG_eq (box : Rho5.Algebraic.CandidateBox x y z g) :
    stageG x y z g = matrixG x y z := by
  rw [stageG, stageF_eq box, schur_matrixF box]

theorem stageH_eq (box : Rho5.Algebraic.CandidateBox x y z g) :
    stageH x y z g = matrixH x y z := by
  rw [stageH, stageG_eq box, schur_matrixG box]

theorem candidate_00 (x y z g : ℝ) : candidateMatrix x y z g 0 0 = 1 := rfl

theorem stageF_00 (box : Rho5.Algebraic.CandidateBox x y z g) :
    stageF x y z g 0 0 = 1+z := by
  rw [stageF_eq box]
  rfl

theorem p3_eq (box : Rho5.Algebraic.CandidateBox x y z g) :
    p3 x y z g = corePivot x y z := by
  rw [p3, stageG_eq box]
  rfl

theorem stageH_00 (box : Rho5.Algebraic.CandidateBox x y z g) :
    stageH x y z g 0 0 = halfHeight x y z := by
  rw [stageH_eq box]
  rfl

end Rho5.ExternalAttainment
