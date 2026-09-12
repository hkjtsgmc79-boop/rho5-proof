import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! A finite-dimensional Neumann argument. All norms here are the norm on E,
not the entry maximum of a matrix. Specializing E to `Fin n → ℝ` gives vector
sup norm; the hypothesis is the corresponding induced operator bound. -/
namespace Rho5.LocalAnalysis
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A whole-domain residual estimate, whenever established at a point, proves
invertibility there. No inverse or injectivity is assumed. -/
theorem bijective_of_residual (J C : E →ₗ[ℝ] E) {q : ℝ} (hq : q < 1)
    (hres : ∀ v, ‖v - C (J v)‖ ≤ q * ‖v‖) : Function.Bijective J := by
  have hinj : Function.Injective J := by
    intro x y hxy
    have h := hres (x - y)
    have hz : J (x - y) = 0 := by simp [map_sub, hxy]
    simp only [hz, map_zero, sub_zero] at h
    have hn : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The inverse direction and its usual one-term Neumann bound. -/
theorem inverse_direction (J C : E →ₗ[ℝ] E) {q : ℝ} (hq : q < 1)
    (hres : ∀ v, ‖v - C (J v)‖ ≤ q * ‖v‖) (b : E) :
    ∃! v, J v = b ∧ ‖v‖ ≤ ‖C b‖ / (1 - q) := by
  obtain ⟨hinj, hsurj⟩ := bijective_of_residual J C hq hres
  obtain ⟨v, hv⟩ := hsurj b
  have hr := hres v
  rw [hv] at hr
  have ht : ‖v‖ ≤ ‖v - C b‖ + ‖C b‖ := by
    simpa using norm_add_le (v - C b) (C b)
  have hb : ‖v‖ ≤ ‖C b‖ / (1 - q) := by
    apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
    nlinarith
  refine ⟨v, ⟨hv, hb⟩, ?_⟩
  intro w hw
  exact hinj (hw.1.trans hv.symm)

/-- The actual second-order remainder used by V43: for E=I-CJ and v0=Cb,
v = v0 + E v0 + remainder, with remainder bounded by n q²/(1-q). -/
theorem second_order_remainder (J C : E →ₗ[ℝ] E) {q n : ℝ}
    (hq0 : 0 ≤ q) (hq : q < 1)
    (hres : ∀ v, ‖v - C (J v)‖ ≤ q * ‖v‖)
    (b v : E) (hv : J v = b) (hn : ‖C b‖ ≤ n) :
    ‖v - (C b + (C b - C (J (C b))))‖ ≤ n * q ^ 2 / (1 - q) := by
  let R : E →ₗ[ℝ] E := LinearMap.id - C.comp J
  have hR (w : E) : ‖R w‖ ≤ q * ‖w‖ := hres w
  have hRv : R v = v - C b := by simp [R, hv]
  have hrem : v - (C b + (C b - C (J (C b)))) = R (R v) := by
    rw [hRv]
    simp only [map_sub]
    simp [R, hv]
    abel
  have ht : ‖v‖ ≤ ‖v - C b‖ + ‖C b‖ := by
    simpa using norm_add_le (v - C b) (C b)
  have hr := hres v
  rw [hv] at hr
  have hvbound : ‖v‖ ≤ n / (1 - q) := by
    apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
    nlinarith
  rw [hrem]
  calc
    ‖R (R v)‖ ≤ q * ‖R v‖ := hR _
    _ ≤ q * (q * ‖v‖) := mul_le_mul_of_nonneg_left (hR _) hq0
    _ ≤ q * (q * (n / (1 - q))) := by gcongr
    _ = n * q ^ 2 / (1 - q) := by ring

end
end Rho5.LocalAnalysis
