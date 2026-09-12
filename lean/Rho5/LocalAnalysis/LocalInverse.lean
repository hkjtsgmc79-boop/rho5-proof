import Rho5.LocalAnalysis.SampleData
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

namespace Rho5.LocalAnalysis
noncomputable section
open Filter
open scoped Topology

theorem Expr.hasStrictFDerivAt (a : Expr) (z : X) :
    HasStrictFDerivAt a.eval (a.differential z) z := by
  induction a with
  | const c => exact hasStrictFDerivAt_const (c : ℝ) z
  | var i => exact (coord i).hasStrictFDerivAt
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | neg a ha => exact ha.neg

namespace V43

theorem chart_hasStrictFDerivAt (z : X) : HasStrictFDerivAt chart (chartD z) z :=
  hasStrictFDerivAt_pi.mpr (fun i => (activeExpr i).hasStrictFDerivAt z)

/-- A genuine 21-variable chart on the affine slice fixing the source's own p. -/
def localChart (z : X) (y : Y) : Y := chart (z + tangentLift y)

theorem localChart_hasStrictFDerivAt (z : X) (y : Y) :
    HasStrictFDerivAt (localChart z) (jacobian (z + tangentLift y)) y := by
  have h := (chart_hasStrictFDerivAt (z + tangentLift y)).comp y
    ((hasStrictFDerivAt_const (𝕜 := ℝ) z y).add tangentLift.hasStrictFDerivAt)
  simpa only [zero_add] using h

def jacobianEquiv (h : WholeBoxResidual) (z : X) (hz : z ∈ cube center radius) : Y ≃L[ℝ] Y :=
  ContinuousLinearEquiv.ofBijective (jacobian z)
    (LinearMap.ker_eq_bot.mpr (wholeBox_inverse h z hz).1)
    (LinearMap.range_eq_top.mpr (wholeBox_inverse h z hz).2)

@[simp] theorem jacobianEquiv_apply (h : WholeBoxResidual) (z : X)
    (hz : z ∈ cube center radius) (v : Y) : jacobianEquiv h z hz v = jacobian z v := rfl

/-- Conditional on the displayed whole-box residual certificate, the actual
polynomial chart has a differentiable local inverse on the fixed-p slice.
This proves local existence/regularity, but not finite-time continuation. -/
theorem actual_local_inverse (h : WholeBoxResidual) (z : X) (hz : z ∈ cube center radius) :
    ∃ g : Y → Y,
      g (chart z) = 0 ∧ ContinuousAt g (chart z) ∧
      (∀ᶠ b in 𝓝 (chart z), localChart z (g b) = b) ∧
      HasStrictFDerivAt g ((jacobianEquiv h z hz).symm : Y →L[ℝ] Y) (chart z) := by
  have hd : HasStrictFDerivAt (localChart z) (jacobianEquiv h z hz : Y →L[ℝ] Y) 0 := by
    convert localChart_hasStrictFDerivAt z 0 using 1
    simp [jacobianEquiv, ContinuousLinearEquiv.coe_ofBijective]
  refine ⟨hd.localInverse (localChart z) (jacobianEquiv h z hz) 0, ?_, ?_, ?_, ?_⟩
  · simpa [localChart] using hd.localInverse_apply_image
  · simpa [localChart] using hd.localInverse_continuousAt
  · simpa [localChart] using hd.eventually_right_inverse
  · simpa [localChart] using hd.to_localInverse

/-- O22- is row 19 of the actual replacement chart. -/
def consumeBasis : Y := Pi.single 19 1

def inverseDirection (h : WholeBoxResidual) (z : X) (hz : z ∈ cube center radius) : Y :=
  (jacobianEquiv h z hz).symm consumeBasis

def inward (h : WholeBoxResidual) (z : X) (hz : z ∈ cube center radius) : X :=
  -tangentLift (inverseDirection h z hz)

theorem inverseDirection_equation (h : WholeBoxResidual) (z : X)
    (hz : z ∈ cube center radius) : jacobian z (inverseDirection h z hz) = consumeBasis :=
  (jacobianEquiv h z hz).apply_symm_apply consumeBasis

theorem inward_chart_equation (h : WholeBoxResidual) (z : X)
    (hz : z ∈ cube center radius) : chartD z (inward h z hz) = -consumeBasis := by
  simp only [inward, map_neg]
  exact congrArg Neg.neg (inverseDirection_equation h z hz)

theorem inward_fixes_p (h : WholeBoxResidual) (z : X)
    (hz : z ∈ cube center radius) : inward h z hz 7 = 0 := by simp [inward]

theorem heldGuardD_chartD (z v : X) : chartD z v 15 = heldGuardD z v := by
  simp [chartD, activeExpr, Expr.differential, Expr.eval, heldGuardD, coord]

theorem consumedD_chartD (z v : X) : chartD z v 19 = consumedD z v := by
  simp [chartD, activeExpr, Expr.differential, Expr.eval, consumedD, coord]
  ring

theorem inward_keeps_boundary (h : WholeBoxResidual) (z : X)
    (hz : z ∈ cube center radius) : heldGuardD z (inward h z hz) = 0 := by
  rw [← heldGuardD_chartD, inward_chart_equation]
  simp [consumeBasis]

theorem inward_consumes (h : WholeBoxResidual) (z : X)
    (hz : z ∈ cube center radius) : consumedD z (inward h z hz) = -1 := by
  rw [← consumedD_chartD, inward_chart_equation]
  simp [consumeBasis]

end V43
end
end Rho5.LocalAnalysis
