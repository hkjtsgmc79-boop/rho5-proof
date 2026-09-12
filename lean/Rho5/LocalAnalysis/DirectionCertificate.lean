import Rho5.LocalAnalysis.Direction.ApproxBound
import Rho5.LocalAnalysis.Direction.HeightBound
import Rho5.LocalAnalysis.Direction.GuardBound

/-! Actual V43 case-0 replacement-chart rates. The only analytic certificate
parameter here is the displayed whole-cube residual proposition; no speed,
height-gain, or released-guard estimate is assumed. -/
namespace Rho5.LocalAnalysis.V43
noncomputable section

theorem directionApprox_lift_error (h : WholeBoxResidual) (z : X)
    (hz : z ∈ cube center radius) :
    ‖tangentLift (inverseDirection h z hz) - tangentLift (directionApprox z)‖ ≤
      (17 / 200 : ℝ) := by
  rw [← map_sub]
  exact (tangentLift_norm_le _).trans (directionApprox_error h z hz)

theorem inward_speed (h : WholeBoxResidual) (z : X) (hz : z ∈ cube center radius) :
    ‖inward h z hz‖ ≤ (9 / 4 : ℝ) := by
  have he := directionApprox_error h z hz
  have ha := directionApprox_bound z hz
  have ht : ‖inverseDirection h z hz‖ ≤
      ‖inverseDirection h z hz - directionApprox z‖ + ‖directionApprox z‖ := by
    simpa using norm_add_le (inverseDirection h z hz - directionApprox z) (directionApprox z)
  rw [inward, norm_neg]
  have hl := tangentLift_norm_le (inverseDirection h z hz)
  linarith

theorem inward_height (h : WholeBoxResidual) (z : X) (hz : z ∈ cube center radius) :
    (1 / 16 : ℝ) ≤ heightD (inward h z hz) := by
  have he := directionApprox_error h z hz
  have ha := directionApprox_height_lower z hz
  have hc (i : Fin 21) : |inverseDirection h z hz i - directionApprox z i| ≤
      (17 / 200 : ℝ) := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      (norm_le_pi_norm (inverseDirection h z hz - directionApprox z) i).trans he
  obtain ⟨hl1, hu1⟩ := abs_le.mp (hc 1)
  obtain ⟨hl2, hu2⟩ := abs_le.mp (hc 2)
  change (6 / 25 : ℝ) ≤ -(directionApprox z 1 - directionApprox z 2) at ha
  change (1 / 16 : ℝ) ≤ -(inverseDirection h z hz 1) - -(inverseDirection h z hz 2)
  linarith

theorem inward_released_guard (h : WholeBoxResidual) (z : X)
    (hz : z ∈ cube center radius) :
    (2 / 5 : ℝ) ≤ releasedGuardD z (inward h z hz) := by
  have he := directionApprox_lift_error h z hz
  have ha := directionApprox_guard_lower z hz
  have hg := actual_released_gradient_bound z hz
    (tangentLift (inverseDirection h z hz) - tangentLift (directionApprox z))
  have hm := mul_le_mul_of_nonneg_left he
    (by norm_num : (0 : ℝ) ≤ 1818237624 / 1000000000)
  have herr := hg.trans hm
  rw [map_sub] at herr
  obtain ⟨hl, hu⟩ := abs_le.mp herr
  rw [inward, map_neg]
  linarith

/-- All three quantitative rates of the actual inward field on the full cube. -/
theorem inward_rates (h : WholeBoxResidual) (z : X) (hz : z ∈ cube center radius) :
    ‖inward h z hz‖ ≤ (9 / 4 : ℝ) ∧
    (1 / 16 : ℝ) ≤ heightD (inward h z hz) ∧
    (2 / 5 : ℝ) ≤ releasedGuardD z (inward h z hz) :=
  ⟨inward_speed h z hz, inward_height h z hz, inward_released_guard h z hz⟩

#print axioms inward_rates
end
end Rho5.LocalAnalysis.V43
