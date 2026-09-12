import Rho5.ExternalV43Existence.Regularity
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Actual trajectory on a time neighborhood of the requested finite interval

The pinned mathlib version defines the public Picard-Lindelöf existence
interface in `Mathlib.Analysis.ODE.PicardLindelof`, not in a later ExistUnique file.
A strictly larger time interval supplies ordinary derivatives at both endpoints.
-/

namespace Rho5.ExternalV43Existence
noncomputable section
open Rho5.LocalAnalysis Rho5.LocalAnalysis.V43 Set Metric
open scoped NNReal Topology

/-- Stronger than A1: the genuine ODE holds on an open time interval containing
[0,T].  Physical feasibility is only subsequently claimed on the resource-limited
interval [0,T], not on this whole open time interval. -/
theorem exists_actual_trajectory_on_time_neighborhood (z0 : X) {T d : ℝ}
    (hT : 0 ≤ T) (hstart : z0 ∈ cube center d)
    (hbudget : d + (9 / 4 : ℝ) * T < radius) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → X, γ 0 = z0 ∧
      ∀ t ∈ Ioo (-ε) (T + ε), HasDerivAt γ (certifiedField (γ t)) t := by
  let m : ℝ := radius - d - (9 / 4 : ℝ) * T
  let a : ℝ := (9 / 4 : ℝ) * T + m / 2
  let ε : ℝ := m / 9
  have hmarg := finite_horizon_margins hT hbudget
  change 0 < m ∧ 0 < a ∧ 0 < ε ∧ d + a < radius ∧
    (9 / 4 : ℝ) * (T + ε) ≤ a at hmarg
  rcases hmarg with ⟨hm, ha, hε, hspace, htime⟩
  have hsub : closedBall z0 a ⊆ cube center radius :=
    closedBall_subset_cube hstart hspace.le
  obtain ⟨K, hK⟩ := certifiedField_lipschitz_on_closedBall z0 a hsub
  let aNN : ℝ≥0 := ⟨a, ha.le⟩
  let speedNN : ℝ≥0 := ⟨(9 / 4 : ℝ), by norm_num⟩
  let t0 : Icc (-ε) (T + ε) := ⟨0, by constructor <;> linarith⟩
  have hPL : IsPicardLindelof (fun (_ : ℝ) => certifiedField)
      t0 z0 aNN 0 speedNN K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      exact hK
    · intro z hz
      exact continuousOn_const
    · intro t ht z hz
      exact certifiedField_speed z
    · change (9 / 4 : ℝ) * max ((T + ε) - 0) (0 - (-ε)) ≤ a - 0
      have hmax : max (T + ε) ε = T + ε := max_eq_left (by linarith)
      simpa only [sub_zero, sub_neg_eq_add, zero_add, hmax] using htime
  obtain ⟨γ, hγ0, hγ⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨ε, hε, γ, hγ0, ?_⟩
  intro t ht
  exact (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- A1. No trajectory, path-invariance or regularity assumption occurs in the
inputs.  The original certified field is the derivative, including at 0 and T. -/
theorem exists_actual_trajectory (z0 : X) {T d : ℝ}
    (hT : 0 ≤ T) (hstart : z0 ∈ cube center d)
    (hbudget : d + (9 / 4 : ℝ) * T < radius) :
    ∃ γ : ℝ → X, γ 0 = z0 ∧
      ∀ t ∈ Icc 0 T, HasDerivAt γ (certifiedField (γ t)) t := by
  obtain ⟨ε, hε, γ, hγ0, hγ⟩ :=
    exists_actual_trajectory_on_time_neighborhood z0 hT hstart hbudget
  refine ⟨γ, hγ0, ?_⟩
  intro t ht
  apply hγ t
  constructor <;> linarith [ht.1, ht.2]

/-- Explicit endpoint regression: T=0 still has the prescribed derivative.
A constant path would not in general satisfy this assertion. -/
theorem exists_zero_time_actual_derivative (z0 : X) {d : ℝ}
    (hstart : z0 ∈ cube center d) (hbudget : d < radius) :
    ∃ γ : ℝ → X, γ 0 = z0 ∧ HasDerivAt γ (certifiedField z0) 0 := by
  obtain ⟨γ, h0, hd⟩ := exists_actual_trajectory z0 (T := 0)
    (by norm_num) hstart (by simpa using hbudget)
  refine ⟨γ, h0, ?_⟩
  simpa only [h0] using hd 0 ⟨le_rfl, le_rfl⟩

end
end Rho5.ExternalV43Existence
