import Rho5.ExternalV43Existence.Trajectory

/-!
# Physical consequences for the same actual trajectory

These are existential wrappers over the supplied, already conditional V43
finite-trip theorems.  The ODE is now a conclusion, not a hypothesis.
-/

namespace Rho5.ExternalV43Existence
noncomputable section
open Rho5.LocalAnalysis Rho5.LocalAnalysis.V43 Set

/-- A2. The actual source and a single actual trajectory satisfy all eight
physical/quantitative conclusions simultaneously throughout the closed interval. -/
theorem exists_physical_trajectory (z0 : X) {T d : ℝ}
    (hT : 0 ≤ T) (hstart : z0 ∈ cube center d)
    (hbudget : d + (9 / 4 : ℝ) * T < radius)
    (hsource : Physical z0) (hresource : T ≤ consumed z0) :
    ∃ γ : ℝ → X, γ 0 = z0 ∧
      (∀ t ∈ Icc 0 T, HasDerivAt γ (certifiedField (γ t)) t) ∧
      ∀ t ∈ Icc 0 T,
        γ t ∈ cube center radius ∧
        ‖γ t - z0‖ ≤ (9 / 4 : ℝ) * t ∧
        height z0 + t / 16 ≤ height (γ t) ∧
        heldGuard (γ t) = heldGuard z0 ∧
        releasedGuard z0 + (2 / 5 : ℝ) * t ≤ releasedGuard (γ t) ∧
        consumed (γ t) = consumed z0 - t ∧
        γ t 7 = z0 7 ∧ Physical (γ t) := by
  obtain ⟨γ, h0, hd⟩ := exists_actual_trajectory z0 hT hstart hbudget
  have hstart' : γ 0 ∈ cube center d := by simpa only [h0] using hstart
  have hsource' : Physical (γ 0) := by simpa only [h0] using hsource
  have hresource' : T ≤ consumed (γ 0) := by simpa only [h0] using hresource
  have htrip := certified_finite_trip γ hT hstart' hbudget hsource' hresource' hd
  refine ⟨γ, h0, hd, ?_⟩
  simpa only [h0] using htrip

/-- A3. The actual ODE reaches the closed resource-exhaustion endpoint.
The initial point and the full ODE assertion remain visible in the conclusion. -/
theorem exists_resource_endpoint (z0 : X) {T d : ℝ}
    (hT : 0 ≤ T) (hstart : z0 ∈ cube center d)
    (hbudget : d + (9 / 4 : ℝ) * T < radius)
    (hsource : Physical z0) (hresource : T = consumed z0) :
    ∃ γ : ℝ → X, γ 0 = z0 ∧
      (∀ t ∈ Icc 0 T, HasDerivAt γ (certifiedField (γ t)) t) ∧
      consumed (γ T) = 0 ∧ Physical (γ T) := by
  obtain ⟨γ, h0, hd⟩ := exists_actual_trajectory z0 hT hstart hbudget
  have hstart' : γ 0 ∈ cube center d := by simpa only [h0] using hstart
  have hsource' : Physical (γ 0) := by simpa only [h0] using hsource
  have hresource' : T = consumed (γ 0) := by simpa only [h0] using hresource
  have hend := certified_resource_endpoint γ hT hstart' hbudget hsource' hresource' hd
  exact ⟨γ, h0, hd, hend⟩

/-- Resource-time specialization: the time is the source's own consumed slack. -/
theorem exists_exhaustion_at_own_resource (z0 : X) {d : ℝ}
    (hresource : 0 ≤ consumed z0) (hstart : z0 ∈ cube center d)
    (hbudget : d + (9 / 4 : ℝ) * consumed z0 < radius)
    (hsource : Physical z0) :
    ∃ γ : ℝ → X, γ 0 = z0 ∧
      (∀ t ∈ Icc 0 (consumed z0), HasDerivAt γ (certifiedField (γ t)) t) ∧
      consumed (γ (consumed z0)) = 0 ∧ Physical (γ (consumed z0)) := by
  exact exists_resource_endpoint z0 hresource hstart hbudget hsource rfl

/-- A physical point on P0-=0 is allowed as an initial state.
No strict inequality for the physical guard is introduced. -/
theorem exists_guard_boundary_trajectory (z0 : X) {T d : ℝ}
    (hT : 0 ≤ T) (hstart : z0 ∈ cube center d)
    (hbudget : d + (9 / 4 : ℝ) * T < radius)
    (hsource : Physical z0) (hresource : T ≤ consumed z0)
    (hboundary : heldGuard z0 = 0) :
    ∃ γ : ℝ → X, γ 0 = z0 ∧
      (∀ t ∈ Icc 0 T, HasDerivAt γ (certifiedField (γ t)) t) ∧
      ∀ t ∈ Icc 0 T, heldGuard (γ t) = 0 ∧ Physical (γ t) := by
  obtain ⟨γ, h0, hd, htrip⟩ :=
    exists_physical_trajectory z0 hT hstart hbudget hsource hresource
  refine ⟨γ, h0, hd, ?_⟩
  intro t ht
  rcases htrip t ht with ⟨_, _, _, hheld, _, _, _, hphys⟩
  exact ⟨hheld.trans hboundary, hphys⟩

/-- Optional thin compensation wrapper.  The complete-X height bound is an
explicit input and is NOT established by this module.  Trajectory existence,
physicality and the gain estimate are supplied by A1/A2, not by the caller. -/
theorem height_le_of_actual_trip (z0 : X) {T d loss sourceHeight α : ℝ}
    (hT : 0 ≤ T) (hstart : z0 ∈ cube center d)
    (hbudget : d + (9 / 4 : ℝ) * T < radius)
    (hsource : Physical z0) (hresource : T ≤ consumed z0)
    (hupper : ∀ z : X, z ∈ cube center radius → Physical z → height z ≤ α)
    (hpay : 16 * loss ≤ T) (hheight : sourceHeight = height z0 + loss) :
    sourceHeight ≤ α := by
  obtain ⟨γ, h0, _hd, htrip⟩ :=
    exists_physical_trajectory z0 hT hstart hbudget hsource hresource
  rcases htrip T ⟨hT, le_rfl⟩ with ⟨hbox, _, hgain, _, _, _, _, hphys⟩
  apply finite_endpoint_compensation γ
    (T := T) (loss := loss) (sourceHeight := sourceHeight) (α := α)
  · simpa only [h0] using hgain
  · exact hupper (γ T) hbox hphys
  · exact hpay
  · simpa only [h0] using hheight

end
end Rho5.ExternalV43Existence
