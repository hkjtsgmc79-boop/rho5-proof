import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[43] = S11+.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_43 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 43).eval z := by
  have he : inactiveExpr 43 = (.add (.add (.add (.mul (.const (1 / 1)) (.var 7)) (.mul (.const (-1 / 1)) (.var 1))) (.mul (.mul (.const (-1 / 1)) (.var 3)) (.var 5))) (.mul (.mul (.const (-1 / 1)) (.var 14)) (.var 20))) := rfl
  have h := centered_quadratic_lower (80635494946674297 / 100000000000000000)
    (![(-1 / 1), (-1 / 1), (10833981 / 62500000), (1 / 1), (639940483 / 500000000), (-194712659 / 200000000)] : Fin 6 → ℝ) (![(z 1 - (2066258539 / 1000000000)), (z 3 - (-10833981 / 62500000)), (z 5 - (1 / 1)), (z 7 - (726612331 / 500000000)), (z 14 - (194712659 / 200000000)), (z 20 - (-639940483 / 500000000))] : Fin 6 → ℝ) (![(-1 / 1), (-1 / 1)] : Fin 2 → ℝ) (![(z 3 - (-10833981 / 62500000)), (z 14 - (194712659 / 200000000))] : Fin 2 → ℝ) (![(z 5 - (1 / 1)), (z 20 - (-639940483 / 500000000))] : Fin 2 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 1
    · exact hz 3
    · exact hz 5
    · exact hz 7
    · exact hz 14
    · exact hz 20)
    (by
    intro i
    fin_cases i
    · exact hz 3
    · exact hz 14)
    (by
    intro i
    fin_cases i
    · exact hz 5
    · exact hz 20)
  have hx : (inactiveExpr 43).eval z = (80635494946674297 / 100000000000000000) + (∑ i, (![(-1 / 1), (-1 / 1), (10833981 / 62500000), (1 / 1), (639940483 / 500000000), (-194712659 / 200000000)] : Fin 6 → ℝ) i * (![(z 1 - (2066258539 / 1000000000)), (z 3 - (-10833981 / 62500000)), (z 5 - (1 / 1)), (z 7 - (726612331 / 500000000)), (z 14 - (194712659 / 200000000)), (z 20 - (-639940483 / 500000000))] : Fin 6 → ℝ) i) + (∑ i, (![(-1 / 1), (-1 / 1)] : Fin 2 → ℝ) i * (![(z 3 - (-10833981 / 62500000)), (z 14 - (194712659 / 200000000))] : Fin 2 → ℝ) i * (![(z 5 - (1 / 1)), (z 20 - (-639940483 / 500000000))] : Fin 2 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (80635494946674297 / 100000000000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(-1 / 1), (-1 / 1), (10833981 / 62500000), (1 / 1), (639940483 / 500000000), (-194712659 / 200000000)] : Fin 6 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(-1 / 1), (-1 / 1)] : Fin 2 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
