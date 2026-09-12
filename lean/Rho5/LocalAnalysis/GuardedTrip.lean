import Rho5.LocalAnalysis.LocalInverse
import Rho5.LocalAnalysis.FiniteTrip
import Rho5.LocalAnalysis.PhysicalCover

namespace Rho5.LocalAnalysis.V43
noncomputable section
open Set

/-- The actual full chart equation integrates all selected constraints, not
merely the held boundary and consumed coordinate. -/
theorem chart_evolution (γ velocity : ℝ → X) {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt γ (velocity t) t)
    (hchart : ∀ t ∈ Icc 0 T, chartD (γ t) (velocity t) = -consumeBasis) :
    ∀ t ∈ Icc 0 T, ∀ i, chart (γ t) i = chart (γ 0) i - consumeBasis i * t := by
  intro t ht i
  have hrow : ∀ s ∈ Icc 0 T, HasDerivAt (fun s => chart (γ s) i) (-consumeBasis i) s := by
    intro s hs
    have h := ((activeExpr i).hasFDerivAt (γ s)).comp_hasDerivAt s (hd s hs)
    have heq : (activeExpr i).differential (γ s) (velocity s) = -consumeBasis i :=
      congrFun (hchart s hs) i
    rw [heq] at h
    exact h
  have h := scalar_affine_on_trip hT hrow t ht
  linarith

/-- For an actual physical source, a trajectory obeying the chosen chart and
released-guard laws stays in the complete polynomial physical subset, provided
the 78 inactive whole-cube inequalities are certified and the slack lasts. -/
theorem physical_on_trip (γ : ℝ → X) {T : ℝ} (hsource : Physical (γ 0))
    (hbox : InactiveBox)
    (hinside : ∀ t ∈ Icc 0 T, γ t ∈ cube center radius)
    (hchart : ∀ t ∈ Icc 0 T, ∀ i, chart (γ t) i = chart (γ 0) i - consumeBasis i * t)
    (hrel : ∀ t ∈ Icc 0 T,
      releasedGuard (γ 0) + (2 / 5 : ℝ) * t ≤ releasedGuard (γ t))
    (hresource : T ≤ consumed (γ 0)) :
    ∀ t ∈ Icc 0 T, Physical (γ t) := by
  intro t ht
  apply physical_of_chart
  · intro i
    rw [hchart t ht i]
    by_cases hi : i = 19
    · subst i
      simp only [consumeBasis, Pi.single_eq_same, one_mul]
      rw [consumed_chart_meaning]
      linarith [ht.2]
    · have h0 := hsource.chart_nonneg i
      simpa [consumeBasis, hi, Ne.symm hi] using h0
  · have hr0 := hsource.released_nonneg
    nlinarith [hrel t ht, ht.1]
  · exact hbox (γ t) (hinside t ht)

/-- All 21 chart differential laws for a path using the actual inverse field. -/
theorem inverse_field_chart_laws (h : WholeBoxResidual) (γ velocity : ℝ → X) {T : ℝ}
    (hinside : ∀ t ∈ Icc 0 T, γ t ∈ cube center radius)
    (hfield : ∀ t (ht : t ∈ Icc 0 T), velocity t = inward h (γ t) (hinside t ht)) :
    ∀ t ∈ Icc 0 T, chartD (γ t) (velocity t) = -consumeBasis := by
  intro t ht
  rw [hfield t ht]
  exact inward_chart_equation h (γ t) (hinside t ht)

end
end Rho5.LocalAnalysis.V43
