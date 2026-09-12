import Rho5.Algebraic.CriticalExistence.Compatibility
-- D30 adapter note (2026-09-12): the coordinator's latest division of labour replaces the
-- old `Rho5.Algebraic.AlphaRoot` top-level provider with the frozen D34 delivery
-- `outputs/d34_actual_alpha_bridge_20260912`, whose provider theorem is
--   `Rho5.Algebraic.ScalarCandidateAlpha.candidate_system_eq_actual_alpha
--      (x y z g) hb h1 h2 h3 hJ : g = AlphaRoot.alpha`
-- Only this call site changed; the exported statements below are unchanged.
import Rho5.Algebraic.ScalarCandidateAlpha

namespace Rho5.Algebraic.CriticalExistence
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 262144

theorem criticalPoint_g_eq_alpha :
    criticalPoint 3 = Rho5.Algebraic.AlphaRoot.alpha := by
  obtain ⟨hb,h1,h2,h3,hj⟩ := criticalPoint_original
  exact Rho5.Algebraic.ScalarCandidateAlpha.candidate_system_eq_actual_alpha
    (criticalPoint 0) (criticalPoint 1) (criticalPoint 2) (criticalPoint 3)
    hb h1 h2 h3 hj

theorem exists_critical_at_actual_alpha :
    ∃ x y z : ℝ,
      Rho5.Algebraic.CandidateBox x y z Rho5.Algebraic.AlphaRoot.alpha ∧
      Rho5.Algebraic.P1 x y z Rho5.Algebraic.AlphaRoot.alpha=0 ∧
      Rho5.Algebraic.P2 x y z Rho5.Algebraic.AlphaRoot.alpha=0 ∧
      Rho5.Algebraic.P3 x y z Rho5.Algebraic.AlphaRoot.alpha=0 ∧
      Rho5.Algebraic.J x y z Rho5.Algebraic.AlphaRoot.alpha=0 := by
  refine ⟨criticalPoint 0,criticalPoint 1,criticalPoint 2,?_⟩
  simpa only [OriginalCritical,criticalPoint_g_eq_alpha] using criticalPoint_original

end
end Rho5.Algebraic.CriticalExistence
