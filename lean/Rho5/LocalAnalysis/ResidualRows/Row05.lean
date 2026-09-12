import Rho5.LocalAnalysis.ResidualTerms
namespace Rho5.LocalAnalysis.V43
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def residualRow5 : List ResidualTerm := [
  ((-250000000 / 518617093), 5, 0),
  ((-250000000 / 518617093), 0, 5)]
theorem residualRow5_identity (z : X) (v : Y) :
    (v - preconditioner (jacobian z v)) 5 = evalTerms z v residualRow5 := by
  simp [preconditioner, preconditionerQ, jacobian, chartD, tangentLift, activeExpr,
    Expr.differential, Expr.eval, coord, Fin.sum_univ_succ, evalTerms, residualRow5, center]
  <;> ring

theorem residualRow5_mass : massTerms residualRow5 * (3 / 1000 : ℚ) ≤ (2345456430874861887039843429154548149516713163290708869117520274418451088946911938485271 / 13009317994696220855310763663665374324696846780979700802579677478003049405906060000000000) := by
  norm_num [massTerms, residualRow5]

theorem residualRow5_bound (z : X) (hz : z ∈ cube center radius) (v : Y) :
    |(v - preconditioner (jacobian z v)) 5| ≤ qBound * ‖v‖ := by
  rw [residualRow5_identity]
  exact checked_mass_bound residualRow5 residualRow5_mass z hz v
end
end Rho5.LocalAnalysis.V43
