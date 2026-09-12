import Rho5.LocalAnalysis.Direction.Common
import Rho5.LocalAnalysis.ResidualRows.Row05
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem directionApprox_row5_identity (z : X) :
    directionApprox z 5 = (-129098687215398198738626441158509120635647439185347043570636750000000000000000 / 1951397699204433128296614549549806148704527017146955120386951621700457410885909) + (129098687215398198738626441158509120635647439185347043570636750000000000000000 / 1951397699204433128296614549549806148704527017146955120386951621700457410885909) * z 5 := by
  change directionBase 5 + (directionBase - preconditioner (jacobian z directionBase)) 5 = _
  rw [residualRow5_identity]
  simp only [evalTerms, residualRow5]
  simp only [directionBase_coord_0, directionBase_coord_1, directionBase_coord_2, directionBase_coord_3, directionBase_coord_4, directionBase_coord_5, directionBase_coord_6, directionBase_coord_7, directionBase_coord_8, directionBase_coord_9, directionBase_coord_10, directionBase_coord_11, directionBase_coord_12, directionBase_coord_13, directionBase_coord_14, directionBase_coord_15, directionBase_coord_16, directionBase_coord_17, directionBase_coord_18, directionBase_coord_19, directionBase_coord_20, directionCenter_coord_0, directionCenter_coord_1, directionCenter_coord_2, directionCenter_coord_3, directionCenter_coord_4, directionCenter_coord_5, directionCenter_coord_6, directionCenter_coord_7, directionCenter_coord_8, directionCenter_coord_9, directionCenter_coord_10, directionCenter_coord_11, directionCenter_coord_12, directionCenter_coord_13, directionCenter_coord_14, directionCenter_coord_15, directionCenter_coord_16, directionCenter_coord_17, directionCenter_coord_18, directionCenter_coord_19, directionCenter_coord_20, directionCenter_coord_21]
  norm_num <;> ring

theorem directionApprox_row5_bound (z : X) (hz : z ∈ cube center radius) :
    |directionApprox z 5| ≤ (43 / 20 : ℝ) := by
  have h := centered_affine_bound (0 / 1) (![(129098687215398198738626441158509120635647439185347043570636750000000000000000 / 1951397699204433128296614549549806148704527017146955120386951621700457410885909)] : Fin 1 → ℝ) (![(1 / 1)] : Fin 1 → ℝ) (![z 5] : Fin 1 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by
    intro i
    fin_cases i
    · exact hz 5)
  have he : directionApprox z 5 = (0 / 1) + ∑ k, (![(129098687215398198738626441158509120635647439185347043570636750000000000000000 / 1951397699204433128296614549549806148704527017146955120386951621700457410885909)] : Fin 1 → ℝ) k * ((![z 5] : Fin 1 → ℝ) k - (![(1 / 1)] : Fin 1 → ℝ) k) := by
    rw [directionApprox_row5_identity]
    norm_num [Fin.sum_univ_succ] <;> ring
  rw [← he] at h
  have hm : |(0 / 1)| + (3 / 1000 : ℝ) * ∑ k, |(![(129098687215398198738626441158509120635647439185347043570636750000000000000000 / 1951397699204433128296614549549806148704527017146955120386951621700457410885909)] : Fin 1 → ℝ) k| ≤ (43 / 20 : ℝ) := by
    norm_num [Fin.sum_univ_succ]
  exact h.trans hm
end
end Rho5.LocalAnalysis.V43
