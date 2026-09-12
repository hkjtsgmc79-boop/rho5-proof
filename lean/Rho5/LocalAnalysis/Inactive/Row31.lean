import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[31] = v1+.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_31 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 31).eval z := by
  have he : inactiveExpr 31 = (.add (.const (1 / 1)) (.mul (.const (-1 / 1)) (.var 17))) := rfl
  have h := centered_quadratic_lower (273387669 / 500000000)
    (![(-1 / 1)] : Fin 1 → ℝ) (![(z 17 - (226612331 / 500000000))] : Fin 1 → ℝ) (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 17)
    (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i)
  have hx : (inactiveExpr 31).eval z = (273387669 / 500000000) + (∑ i, (![(-1 / 1)] : Fin 1 → ℝ) i * (![(z 17 - (226612331 / 500000000))] : Fin 1 → ℝ) i) + (∑ i, (![] : Fin 0 → ℝ) i * (![] : Fin 0 → ℝ) i * (![] : Fin 0 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (273387669 / 500000000) - (3 / 1000 : ℝ) * (∑ i, |(![(-1 / 1)] : Fin 1 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![] : Fin 0 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
