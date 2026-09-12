import Rho5.LocalAnalysis.ResidualTerms
namespace Rho5.LocalAnalysis.V43
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def residualRow7 : List ResidualTerm := [
]
theorem residualRow7_identity (z : X) (v : Y) :
    (v - preconditioner (jacobian z v)) 7 = evalTerms z v residualRow7 := by
  simp [preconditioner, preconditionerQ, jacobian, chartD, tangentLift, activeExpr,
    Expr.differential, Expr.eval, coord, Fin.sum_univ_succ, evalTerms, residualRow7, center]
  <;> ring

theorem residualRow7_mass : massTerms residualRow7 * (3 / 1000 : ℚ) ≤ (2345456430874861887039843429154548149516713163290708869117520274418451088946911938485271 / 13009317994696220855310763663665374324696846780979700802579677478003049405906060000000000) := by
  norm_num [massTerms, residualRow7]

theorem residualRow7_bound (z : X) (hz : z ∈ cube center radius) (v : Y) :
    |(v - preconditioner (jacobian z v)) 7| ≤ qBound * ‖v‖ := by
  rw [residualRow7_identity]
  exact checked_mass_bound residualRow7 residualRow7_mass z hz v
end
end Rho5.LocalAnalysis.V43
