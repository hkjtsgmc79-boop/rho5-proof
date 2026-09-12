import Rho5.LocalAnalysis.SampleData
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Rho5.LocalAnalysis
noncomputable section
open Set

/-- Integration of a lower derivative bound on a specified finite interval. -/
theorem scalar_lower_on_trip {f f' : ℝ → ℝ} {T m : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Icc 0 T, m ≤ f' t) :
    ∀ t ∈ Icc 0 T, f 0 + m * t ≤ f t := by
  have hc : ContinuousOn f (Icc 0 T) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Icc 0 T)) := by
    intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hb' : ∀ t ∈ interior (Icc 0 T), m ≤ deriv f t := by
    intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact hb t (interior_subset ht)
  intro t ht
  have h := (convex_Icc (0 : ℝ) T).mul_sub_le_image_sub_of_le_deriv hc hdiff hb'
    0 ⟨le_rfl, hT⟩ t ht ht.1
  linarith

/-- Constant derivative gives an exact coordinate evolution, including endpoints. -/
theorem scalar_affine_on_trip {f : ℝ → ℝ} {T m : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt f m t) :
    ∀ t ∈ Icc 0 T, f t = f 0 + m * t := by
  have hlo := scalar_lower_on_trip hT hd (fun _ _ => le_rfl)
  have hhi := scalar_lower_on_trip hT (fun t ht => (hd t ht).neg) (fun _ _ => le_rfl)
  intro t ht
  have hl := hlo t ht
  have hu := hhi t ht
  dsimp at hu
  linarith

/-- Conditional finite-trip prototype for the actual V43 replaced chart.
The path and its pointwise differential laws are explicit inputs. ODE existence,
maximal continuation and the other 78 physical inequalities are not hidden here. -/
theorem v43_finite_trip (γ velocity : ℝ → X) {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt γ (velocity t) t)
    (hspeed : ∀ t ∈ Icc 0 T, ‖velocity t‖ ≤ 9 / 4)
    (hheight : ∀ t ∈ Icc 0 T, 1 / 16 ≤ heightD (velocity t))
    (hheld : ∀ t ∈ Icc 0 T, heldGuardD (γ t) (velocity t) = 0)
    (hrel : ∀ t ∈ Icc 0 T, 2 / 5 ≤ releasedGuardD (γ t) (velocity t))
    (hconsume : ∀ t ∈ Icc 0 T, consumedD (γ t) (velocity t) = -1)
    (hp : ∀ t ∈ Icc 0 T, velocity t 7 = 0) :
    ∀ t ∈ Icc 0 T,
      ‖γ t - γ 0‖ ≤ (9 / 4 : ℝ) * t ∧
      height (γ 0) + t / 16 ≤ height (γ t) ∧
      heldGuard (γ t) = heldGuard (γ 0) ∧
      releasedGuard (γ 0) + (2 / 5 : ℝ) * t ≤ releasedGuard (γ t) ∧
      consumed (γ t) = consumed (γ 0) - t ∧
      γ t 7 = γ 0 7 := by
  have hdisp := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => hspeed t (Ico_subset_Icc_self ht))
  have hh := scalar_lower_on_trip hT
    (fun t ht => (height_hasFDerivAt (γ t)).comp_hasDerivAt t (hd t ht)) hheight
  have hg := scalar_affine_on_trip hT (fun t ht => by
    have h := (heldGuard_hasFDerivAt (γ t)).comp_hasDerivAt t (hd t ht)
    rw [hheld t ht] at h
    exact h)
  have hr := scalar_lower_on_trip hT
    (fun t ht => (releasedGuard_hasFDerivAt (γ t)).comp_hasDerivAt t (hd t ht)) hrel
  have hc := scalar_affine_on_trip hT (fun t ht => by
    have h := (consumed_hasFDerivAt (γ t)).comp_hasDerivAt t (hd t ht)
    rw [hconsume t ht] at h
    exact h)
  have hpf := scalar_affine_on_trip hT (fun t ht => by
    have h := (hasFDerivAt_apply (𝕜 := ℝ) (7 : Fin 22) (γ t)).comp_hasDerivAt t (hd t ht)
    simp only [ContinuousLinearMap.proj_apply] at h
    rw [hp t ht] at h
    exact h)
  intro t ht
  refine ⟨?_, ?_, ?_, hr t ht, ?_, ?_⟩
  · simpa only [sub_zero] using hdisp t ht
  · have h := hh t ht
    dsimp at h
    linarith
  · simpa using hg t ht
  · have h := hc t ht
    dsimp at h
    linarith
  · simpa using hpf t ht

/-- The certified speed produces a closed domain and slack budget for any
already constructed trajectory. This does not assert trajectory existence. -/
theorem trip_stays_in_cube (γ : ℝ → X) (c : X) {ρ d T : ℝ}
    (hstart : γ 0 ∈ cube c d) (hbudget : d + (9 / 4 : ℝ) * T ≤ ρ)
    (hdisp : ∀ t ∈ Icc 0 T, ‖γ t - γ 0‖ ≤ (9 / 4 : ℝ) * t) :
    ∀ t ∈ Icc 0 T, γ t ∈ cube c ρ := by
  intro t ht i
  have hi : |γ t i - γ 0 i| ≤ ‖γ t - γ 0‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (γ t - γ 0) i
  have ha := abs_sub_le (γ t i) (γ 0 i) (c i)
  have hb := hdisp t ht
  have hc := hstart i
  nlinarith [ht.2]

/-- Boundary P0-=0 is kept exactly; the released P2+ remains nonnegative;
the consumed O22- remains nonnegative up to its finite exhaustion time. -/
theorem trip_guard_margins (γ : ℝ → X) {T : ℝ}
    (hheld : ∀ t ∈ Icc 0 T, heldGuard (γ t) = heldGuard (γ 0))
    (hrel : ∀ t ∈ Icc 0 T, releasedGuard (γ 0) + (2 / 5 : ℝ) * t ≤ releasedGuard (γ t))
    (hconsume : ∀ t ∈ Icc 0 T, consumed (γ t) = consumed (γ 0) - t)
    (h0 : heldGuard (γ 0) = 0) (hrel0 : 0 ≤ releasedGuard (γ 0))
    (hresource : T ≤ consumed (γ 0)) :
    ∀ t ∈ Icc 0 T, heldGuard (γ t) = 0 ∧
      0 ≤ releasedGuard (γ t) ∧ 0 ≤ consumed (γ t) := by
  intro t ht
  refine ⟨(hheld t ht).trans h0, ?_, ?_⟩
  · nlinarith [hrel t ht, ht.1]
  · rw [hconsume t ht]
    linarith [ht.2]

/-- A reached endpoint pays an actual height loss. The upper bound and endpoint
existence remain explicit, and no transport is assumed to preserve height. -/
theorem finite_endpoint_compensation (γ : ℝ → X) {T loss sourceHeight α : ℝ}
    (hgain : height (γ 0) + T / 16 ≤ height (γ T))
    (htarget : height (γ T) ≤ α) (hpay : 16 * loss ≤ T)
    (hsource : sourceHeight = height (γ 0) + loss) : sourceHeight ≤ α := by
  linarith

end
end Rho5.LocalAnalysis
