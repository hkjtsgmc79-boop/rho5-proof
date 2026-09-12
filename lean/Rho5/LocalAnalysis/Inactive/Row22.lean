import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[22] = O01+.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_22 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 22).eval z := by
  have he : inactiveExpr 22 = (.add (.add (.add (.const (1 / 1)) (.mul (.const (-1 / 1)) (.var 3))) (.mul (.mul (.const (-1 / 1)) (.var 13)) (.var 20))) (.mul (.mul (.const (-1 / 1)) (.var 10)) (.var 17))) := rfl
  have h := centered_quadratic_lower (2 / 1)
    (![(-1 / 1), (-226612331 / 500000000), (639940483 / 500000000), (-1 / 1), (-1 / 1)] : Fin 5 → ℝ) (![(z 3 - (-10833981 / 62500000)), (z 10 - (1 / 1)), (z 13 - (1 / 1)), (z 17 - (226612331 / 500000000)), (z 20 - (-639940483 / 500000000))] : Fin 5 → ℝ) (![(-1 / 1), (-1 / 1)] : Fin 2 → ℝ) (![(z 13 - (1 / 1)), (z 10 - (1 / 1))] : Fin 2 → ℝ) (![(z 20 - (-639940483 / 500000000)), (z 17 - (226612331 / 500000000))] : Fin 2 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 3
    · exact hz 10
    · exact hz 13
    · exact hz 17
    · exact hz 20)
    (by
    intro i
    fin_cases i
    · exact hz 13
    · exact hz 10)
    (by
    intro i
    fin_cases i
    · exact hz 20
    · exact hz 17)
  have hx : (inactiveExpr 22).eval z = (2 / 1) + (∑ i, (![(-1 / 1), (-226612331 / 500000000), (639940483 / 500000000), (-1 / 1), (-1 / 1)] : Fin 5 → ℝ) i * (![(z 3 - (-10833981 / 62500000)), (z 10 - (1 / 1)), (z 13 - (1 / 1)), (z 17 - (226612331 / 500000000)), (z 20 - (-639940483 / 500000000))] : Fin 5 → ℝ) i) + (∑ i, (![(-1 / 1), (-1 / 1)] : Fin 2 → ℝ) i * (![(z 13 - (1 / 1)), (z 10 - (1 / 1))] : Fin 2 → ℝ) i * (![(z 20 - (-639940483 / 500000000)), (z 17 - (226612331 / 500000000))] : Fin 2 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (2 / 1) - (3 / 1000 : ℝ) * (∑ i, |(![(-1 / 1), (-226612331 / 500000000), (639940483 / 500000000), (-1 / 1), (-1 / 1)] : Fin 5 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(-1 / 1), (-1 / 1)] : Fin 2 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
