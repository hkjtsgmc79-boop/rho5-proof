import Rho5.ExternalV43Existence.Geometry
import Rho5.LocalAnalysis.Pilot
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# A membership-independent representation of the certified inverse field

We do not claim that `certifiedField`, with its outside-zero branch, is globally
continuous.  Instead we use the ordinary total CLM inverse as an auxiliary
expression and prove equality with the certified field on the unchanged cube.
-/

namespace Rho5.ExternalV43Existence
noncomputable section
-- D84 lane adaptation (2026-09-12): the `ℝ≥0` notation and the `WithTop ℕ∞` order argument of
-- `ContDiffOn.exists_lipschitzOnWith` need their scopes/annotations; without `NNReal` in scope
-- `ℝ≥0` parses as a comparison and the statement is rejected.  No mathematics is changed.
open scoped NNReal
open Rho5.LocalAnalysis Rho5.LocalAnalysis.V43 Set Metric

/-- Every expression in the actual finite polynomial syntax is C². -/
theorem expr_contDiff_two (a : Expr) : ContDiff ℝ 2 a.eval := by
  induction a with
  | const c => exact contDiff_const
  | var i => exact (coord i).contDiff
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | neg a ha => exact ha.neg

/-- This is the original 21-coordinate chart, not a replacement model. -/
theorem actual_chart_contDiff_two : ContDiff ℝ 2 chart := by
  exact contDiff_pi.mpr (fun i => expr_contDiff_two (activeExpr i))

/-- The supplied syntactic differential is the actual Fréchet derivative. -/
theorem actual_chartD_eq_fderiv : chartD = fderiv ℝ chart := by
  funext z
  exact (chart_hasFDerivAt z).fderiv.symm

/-- Smooth dependence of the supplied, fixed-p Jacobian on all X coordinates. -/
theorem actual_jacobian_contDiff_one : ContDiff ℝ 1 jacobian := by
  have hc : ContDiff ℝ 1 chartD := by
    rw [actual_chartD_eq_fderiv]
    exact actual_chart_contDiff_two.fderiv_right (by norm_num)
  change ContDiff ℝ 1 (fun z : X => (chartD z).comp tangentLift)
  exact hc.clm_comp contDiff_const

/-- An auxiliary total formula.  No smoothness is asserted at singular Jacobians. -/
def inverseFormula (z : X) : X :=
  -tangentLift ((ContinuousLinearMap.inverse (jacobian z)) consumeBasis)

/-- The pointwise proof-dependent inverse agrees with the ordinary total inverse.
The equivalence is obtained from the supplied whole-box certificate. -/
theorem inverseFormula_eq_inward (z : X) (hz : z ∈ cube center radius) :
    inverseFormula z = inward wholeBoxResidual_checked z hz := by
  let e : Y ≃L[ℝ] Y := jacobianEquiv wholeBoxResidual_checked z hz
  have he : (e : Y →L[ℝ] Y) = jacobian z := by
    apply ContinuousLinearMap.ext
    intro v
    exact jacobianEquiv_apply wholeBoxResidual_checked z hz v
  have hinv : ContinuousLinearMap.inverse (jacobian z) = (e.symm : Y →L[ℝ] Y) := by
    rw [← he]
    exact ContinuousLinearMap.inverse_equiv e
  unfold inverseFormula inward inverseDirection
  rw [hinv]
  rfl

/-- Equality is used only on the actual certified cube. -/
theorem inverseFormula_eq_certifiedField (z : X) (hz : z ∈ cube center radius) :
    inverseFormula z = certifiedField z := by
  rw [certifiedField_eq z hz]
  exact inverseFormula_eq_inward z hz

/-- Inversion is C¹ at each certified invertible Jacobian.  This is a regularity
proof, not an assumption that pointwise inverses automatically vary continuously. -/
theorem inverseFormula_contDiffAt (z : X) (hz : z ∈ cube center radius) :
    ContDiffAt ℝ 1 inverseFormula z := by
  let e : Y ≃L[ℝ] Y := jacobianEquiv wholeBoxResidual_checked z hz
  have he : (e : Y →L[ℝ] Y) = jacobian z := by
    apply ContinuousLinearMap.ext
    intro v
    exact jacobianEquiv_apply wholeBoxResidual_checked z hz v
  have hInv : ContDiffAt ℝ 1 ContinuousLinearMap.inverse (jacobian z) := by
    rw [← he]
    exact contDiffAt_map_inverse e
  have hComp : ContDiffAt ℝ 1
      (fun w : X => ContinuousLinearMap.inverse (jacobian w)) z :=
    hInv.comp z actual_jacobian_contDiff_one.contDiffAt
  have hApply : ContDiffAt ℝ 1
      (fun w : X => (ContinuousLinearMap.inverse (jacobian w)) consumeBasis) z :=
    hComp.clm_apply contDiffAt_const
  have hLift : ContDiffAt ℝ 1
      (fun w : X => tangentLift ((ContinuousLinearMap.inverse (jacobian w)) consumeBasis)) z :=
    tangentLift.contDiff.contDiffAt.comp z hApply
  exact hLift.neg

/-- On any compact ball contained in the certified cube there is a finite
Lipschitz constant for the actual field.  It need not be numerically optimized:
Picard-Lindelöf's finite-horizon theorem does not require K*T < 1. -/
theorem certifiedField_lipschitz_on_closedBall (z0 : X) (a : ℝ)
    (hsub : closedBall z0 a ⊆ cube center radius) :
    ∃ K : ℝ≥0, LipschitzOnWith K certifiedField (closedBall z0 a) := by
  have hsmooth : ContDiffOn ℝ 1 inverseFormula (closedBall z0 a) := by
    intro z hz
    exact (inverseFormula_contDiffAt z (hsub hz)).contDiffWithinAt
  obtain ⟨K, hK⟩ := hsmooth.exists_lipschitzOnWith (one_ne_zero : (1 : WithTop ℕ∞) ≠ 0)
    (convex_closedBall z0 a) (isCompact_closedBall z0 a)
  refine ⟨K, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro z hz w hw
  rw [← inverseFormula_eq_certifiedField z (hsub hz),
    ← inverseFormula_eq_certifiedField w (hsub hw)]
  exact hK.dist_le_mul z hz w hw

end
end Rho5.ExternalV43Existence
