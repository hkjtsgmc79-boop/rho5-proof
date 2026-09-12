import Rho5.LocalAnalysis.Direction.Common
import Rho5.LocalAnalysis.ResidualRows.Row11
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem directionApprox_row11_identity (z : X) :
    directionApprox z 11 = (0 : ℝ) := by
  change directionBase 11 + (directionBase - preconditioner (jacobian z directionBase)) 11 = _
  rw [residualRow11_identity]
  simp only [evalTerms, residualRow11]
  simp only [directionBase_coord_0, directionBase_coord_1, directionBase_coord_2, directionBase_coord_3, directionBase_coord_4, directionBase_coord_5, directionBase_coord_6, directionBase_coord_7, directionBase_coord_8, directionBase_coord_9, directionBase_coord_10, directionBase_coord_11, directionBase_coord_12, directionBase_coord_13, directionBase_coord_14, directionBase_coord_15, directionBase_coord_16, directionBase_coord_17, directionBase_coord_18, directionBase_coord_19, directionBase_coord_20, directionCenter_coord_0, directionCenter_coord_1, directionCenter_coord_2, directionCenter_coord_3, directionCenter_coord_4, directionCenter_coord_5, directionCenter_coord_6, directionCenter_coord_7, directionCenter_coord_8, directionCenter_coord_9, directionCenter_coord_10, directionCenter_coord_11, directionCenter_coord_12, directionCenter_coord_13, directionCenter_coord_14, directionCenter_coord_15, directionCenter_coord_16, directionCenter_coord_17, directionCenter_coord_18, directionCenter_coord_19, directionCenter_coord_20, directionCenter_coord_21]
  norm_num <;> ring

theorem directionApprox_row11_bound (z : X) (hz : z ∈ cube center radius) :
    |directionApprox z 11| ≤ (43 / 20 : ℝ) := by
  have h := centered_affine_bound (0 / 1) (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by
    intro i
    fin_cases i)
  have he : directionApprox z 11 = (0 / 1) + ∑ k, (![] : Fin 0 → ℝ) k * ((![] : Fin 0 → ℝ) k - (![] : Fin 0 → ℝ) k) := by
    rw [directionApprox_row11_identity]
    norm_num [Fin.sum_univ_succ] <;> ring
  rw [← he] at h
  have hm : |(0 / 1)| + (3 / 1000 : ℝ) * ∑ k, |(![] : Fin 0 → ℝ) k| ≤ (43 / 20 : ℝ) := by
    norm_num [Fin.sum_univ_succ]
  exact h.trans hm
end
end Rho5.LocalAnalysis.V43
