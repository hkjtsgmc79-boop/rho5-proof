import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[41] = D11+.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_41 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 41).eval z := by
  have he : inactiveExpr 41 = (.add (.add (.mul (.const (1 / 1)) (.var 0)) (.mul (.const (-1 / 1)) (.var 1))) (.mul (.mul (.const (-1 / 1)) (.var 3)) (.var 5))) := rfl
  have h := centered_quadratic_lower (181553529 / 1000000000)
    (![(1 / 1), (-1 / 1), (-1 / 1), (10833981 / 62500000)] : Fin 4 → ℝ) (![(z 0 - (518617093 / 250000000)), (z 1 - (2066258539 / 1000000000)), (z 3 - (-10833981 / 62500000)), (z 5 - (1 / 1))] : Fin 4 → ℝ) (![(-1 / 1)] : Fin 1 → ℝ) (![(z 3 - (-10833981 / 62500000))] : Fin 1 → ℝ) (![(z 5 - (1 / 1))] : Fin 1 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 0
    · exact hz 1
    · exact hz 3
    · exact hz 5)
    (by
    intro i
    fin_cases i
    · exact hz 3)
    (by
    intro i
    fin_cases i
    · exact hz 5)
  have hx : (inactiveExpr 41).eval z = (181553529 / 1000000000) + (∑ i, (![(1 / 1), (-1 / 1), (-1 / 1), (10833981 / 62500000)] : Fin 4 → ℝ) i * (![(z 0 - (518617093 / 250000000)), (z 1 - (2066258539 / 1000000000)), (z 3 - (-10833981 / 62500000)), (z 5 - (1 / 1))] : Fin 4 → ℝ) i) + (∑ i, (![(-1 / 1)] : Fin 1 → ℝ) i * (![(z 3 - (-10833981 / 62500000))] : Fin 1 → ℝ) i * (![(z 5 - (1 / 1))] : Fin 1 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (181553529 / 1000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(1 / 1), (-1 / 1), (-1 / 1), (10833981 / 62500000)] : Fin 4 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(-1 / 1)] : Fin 1 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
