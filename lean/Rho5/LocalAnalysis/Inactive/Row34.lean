import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[34] = q1-.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_34 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 34).eval z := by
  have he : inactiveExpr 34 = (.add (.mul (.const (1 / 1)) (.var 7)) (.mul (.const (1 / 1)) (.var 20))) := rfl
  have h := centered_quadratic_lower (10833981 / 62500000)
    (![(1 / 1), (1 / 1)] : Fin 2 → ℝ) (![(z 7 - (726612331 / 500000000)), (z 20 - (-639940483 / 500000000))] : Fin 2 → ℝ) (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 7
    · exact hz 20)
    (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i)
  have hx : (inactiveExpr 34).eval z = (10833981 / 62500000) + (∑ i, (![(1 / 1), (1 / 1)] : Fin 2 → ℝ) i * (![(z 7 - (726612331 / 500000000)), (z 20 - (-639940483 / 500000000))] : Fin 2 → ℝ) i) + (∑ i, (![] : Fin 0 → ℝ) i * (![] : Fin 0 → ℝ) i * (![] : Fin 0 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (10833981 / 62500000) - (3 / 1000 : ℝ) * (∑ i, |(![(1 / 1), (1 / 1)] : Fin 2 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![] : Fin 0 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
