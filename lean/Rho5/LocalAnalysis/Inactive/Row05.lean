import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[5] = u0-.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_05 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 5).eval z := by
  have he : inactiveExpr 5 = (.add (.const (1 / 1)) (.mul (.const (1 / 1)) (.var 10))) := rfl
  have h := centered_quadratic_lower (2 / 1)
    (![(1 / 1)] : Fin 1 → ℝ) (![(z 10 - (1 / 1))] : Fin 1 → ℝ) (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 10)
    (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i)
  have hx : (inactiveExpr 5).eval z = (2 / 1) + (∑ i, (![(1 / 1)] : Fin 1 → ℝ) i * (![(z 10 - (1 / 1))] : Fin 1 → ℝ) i) + (∑ i, (![] : Fin 0 → ℝ) i * (![] : Fin 0 → ℝ) i * (![] : Fin 0 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (2 / 1) - (3 / 1000 : ℝ) * (∑ i, |(![(1 / 1)] : Fin 1 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![] : Fin 0 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
