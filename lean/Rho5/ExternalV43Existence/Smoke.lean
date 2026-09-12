import Rho5.ExternalV43Existence.Geometry
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.ODE.PicardLindelof

/-! Lightweight API smoke test.  Does not import the large V43 row certificates. -/
namespace Rho5.ExternalV43Existence.Smoke
noncomputable section
open Rho5.LocalAnalysis Set Metric

#check ContinuousLinearMap.inverse_equiv
#check contDiffAt_map_inverse
#check ContDiff.fderiv_right
#check ContDiffOn.exists_lipschitzOnWith
#check IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
#check HasDerivWithinAt.hasDerivAt
#check Icc_mem_nhds

/-- Explicit endpoint conversions, including the requested T=0 situation. -/
example {γ f : ℝ → ℝ} {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε)
    (hd : ∀ t ∈ Icc (-ε) (T + ε),
      HasDerivWithinAt γ (f t) (Icc (-ε) (T + ε)) t) :
    ∀ t ∈ Icc 0 T, HasDerivAt γ (f t) t := by
  intro t ht
  have hi : t ∈ Ioo (-ε) (T + ε) := by constructor <;> linarith [ht.1, ht.2]
  exact (hd t (Ioo_subset_Icc_self hi)).hasDerivAt (Icc_mem_nhds hi.1 hi.2)

example : 0 < ((3 / 1000 : ℝ) - 0 - (9 / 4 : ℝ) * 0) / 9 := by norm_num

example {c z0 : X} {d a ρ : ℝ}
    (h0 : z0 ∈ cube c d) (h : d + a ≤ ρ) :
    closedBall z0 a ⊆ cube c ρ :=
  Rho5.ExternalV43Existence.closedBall_subset_cube h0 h

/-- Finite-dimensional properness is needed only to obtain a finite Lipschitz
constant on a compact ball. -/
example (z0 : X) (a : ℝ) : IsCompact (closedBall z0 a) := isCompact_closedBall z0 a

end
end Rho5.ExternalV43Existence.Smoke
