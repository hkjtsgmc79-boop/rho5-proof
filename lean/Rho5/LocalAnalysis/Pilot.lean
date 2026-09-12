import Rho5.LocalAnalysis.ResidualCertificate
import Rho5.LocalAnalysis.InactiveCertificate
import Rho5.LocalAnalysis.DirectionCertificate
import Rho5.LocalAnalysis.GuardedTrip

namespace Rho5.LocalAnalysis.V43
noncomputable section
open Set

/-- A total extension for stating trajectories. The zero branch is never used
on a trip satisfying the strict displacement budget below. -/
def certifiedField (z : X) : X := by
  classical
  exact if hz : z ∈ cube center radius then inward wholeBoxResidual_checked z hz else 0

theorem certifiedField_eq (z : X) (hz : z ∈ cube center radius) :
    certifiedField z = inward wholeBoxResidual_checked z hz := by
  simp [certifiedField, hz]

theorem certifiedField_speed (z : X) : ‖certifiedField z‖ ≤ (9 / 4 : ℝ) := by
  by_cases hz : z ∈ cube center radius
  · rw [certifiedField_eq z hz]
    exact inward_speed wholeBoxResidual_checked z hz
  · norm_num [certifiedField, hz]

/-- Actual V43 case0 replacement-chart finite-trip prototype. All numerical
rates, whole-cube inverse bounds and 78 inactive inequalities are proved.
The sole trajectory obligation remains explicit as `hd`: this theorem does
not assert the existence or continuation of such a trajectory. The strict
budget proves domain preservation, rather than assuming it along the path. -/
theorem certified_finite_trip (γ : ℝ → X) {T d : ℝ} (hT : 0 ≤ T)
    (hstart : γ 0 ∈ cube center d)
    (hbudget : d + (9 / 4 : ℝ) * T < radius)
    (hsource : Physical (γ 0)) (hresource : T ≤ consumed (γ 0))
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt γ (certifiedField (γ t)) t) :
    ∀ t ∈ Icc 0 T,
      γ t ∈ cube center radius ∧
      ‖γ t - γ 0‖ ≤ (9 / 4 : ℝ) * t ∧
      height (γ 0) + t / 16 ≤ height (γ t) ∧
      heldGuard (γ t) = heldGuard (γ 0) ∧
      releasedGuard (γ 0) + (2 / 5 : ℝ) * t ≤ releasedGuard (γ t) ∧
      consumed (γ t) = consumed (γ 0) - t ∧
      γ t 7 = γ 0 7 ∧ Physical (γ t) := by
  let velocity : ℝ → X := fun t => certifiedField (γ t)
  have hspeed : ∀ t ∈ Icc 0 T, ‖velocity t‖ ≤ (9 / 4 : ℝ) :=
    fun t _ => certifiedField_speed (γ t)
  have hdisp : ∀ t ∈ Icc 0 T, ‖γ t - γ 0‖ ≤ (9 / 4 : ℝ) * t := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (hd t ht).hasDerivWithinAt)
      (fun t _ => certifiedField_speed (γ t))
    intro t ht
    simpa only [sub_zero] using h t ht
  have hinside := trip_stays_in_cube γ center hstart (le_of_lt hbudget) hdisp
  have hfield (t : ℝ) (ht : t ∈ Icc 0 T) :
      velocity t = inward wholeBoxResidual_checked (γ t) (hinside t ht) :=
    certifiedField_eq (γ t) (hinside t ht)
  have hheight : ∀ t ∈ Icc 0 T, 1 / 16 ≤ heightD (velocity t) := by
    intro t ht
    rw [hfield t ht]
    exact inward_height wholeBoxResidual_checked (γ t) (hinside t ht)
  have hheld : ∀ t ∈ Icc 0 T, heldGuardD (γ t) (velocity t) = 0 := by
    intro t ht
    rw [hfield t ht]
    exact inward_keeps_boundary wholeBoxResidual_checked (γ t) (hinside t ht)
  have hrel : ∀ t ∈ Icc 0 T, 2 / 5 ≤ releasedGuardD (γ t) (velocity t) := by
    intro t ht
    rw [hfield t ht]
    exact inward_released_guard wholeBoxResidual_checked (γ t) (hinside t ht)
  have hconsume : ∀ t ∈ Icc 0 T, consumedD (γ t) (velocity t) = -1 := by
    intro t ht
    rw [hfield t ht]
    exact inward_consumes wholeBoxResidual_checked (γ t) (hinside t ht)
  have hp : ∀ t ∈ Icc 0 T, velocity t 7 = 0 := by
    intro t ht
    rw [hfield t ht]
    exact inward_fixes_p wholeBoxResidual_checked (γ t) (hinside t ht)
  have htrip := v43_finite_trip γ velocity hT hd hspeed hheight hheld hrel hconsume hp
  have hchart := chart_evolution γ velocity hT hd
    (inverse_field_chart_laws wholeBoxResidual_checked γ velocity hinside hfield)
  have hphysical := physical_on_trip γ hsource inactiveBox_verified hinside hchart
    (fun t ht => (htrip t ht).2.2.2.1) hresource
  intro t ht
  rcases htrip t ht with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨hinside t ht, h1, h2, h3, h4, h5, h6, hphysical t ht⟩

/-- Exact finite exhaustion once the explicitly supplied trip reaches its
own resource time. No existence assertion is hidden in this statement. -/
theorem certified_resource_endpoint (γ : ℝ → X) {T d : ℝ} (hT : 0 ≤ T)
    (hstart : γ 0 ∈ cube center d) (hbudget : d + (9 / 4 : ℝ) * T < radius)
    (hsource : Physical (γ 0)) (hresource : T = consumed (γ 0))
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt γ (certifiedField (γ t)) t) :
    consumed (γ T) = 0 ∧ Physical (γ T) := by
  have h := certified_finite_trip γ hT hstart hbudget hsource (le_of_eq hresource) hd
    T ⟨hT, le_rfl⟩
  refine ⟨?_, h.2.2.2.2.2.2.2⟩
  rw [h.2.2.2.2.2.1, ← hresource, sub_self]

#print axioms certified_finite_trip
#print axioms certified_resource_endpoint
end
end Rho5.LocalAnalysis.V43
