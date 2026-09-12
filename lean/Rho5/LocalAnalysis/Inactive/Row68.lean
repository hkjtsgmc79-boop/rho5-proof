import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[68] = O21-.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_68 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 68).eval z := by
  have he : inactiveExpr 68 = (.add (.add (.add (.add (.const (1 / 1)) (.mul (.const (1 / 1)) (.var 1))) (.mul (.mul (.const (1 / 1)) (.var 3)) (.var 6))) (.mul (.mul (.const (1 / 1)) (.var 15)) (.var 20))) (.mul (.mul (.const (1 / 1)) (.var 12)) (.var 17))) := rfl
  have h := centered_quadratic_lower (500000000032676797 / 250000000000000000)
    (![(1 / 1), (-47361589 / 1000000000), (-10833981 / 62500000), (226612331 / 500000000), (-639940483 / 500000000), (226612331 / 500000000), (1 / 1)] : Fin 7 → ℝ) (![(z 1 - (2066258539 / 1000000000)), (z 3 - (-10833981 / 62500000)), (z 6 - (-47361589 / 1000000000)), (z 12 - (226612331 / 500000000)), (z 15 - (1 / 1)), (z 17 - (226612331 / 500000000)), (z 20 - (-639940483 / 500000000))] : Fin 7 → ℝ) (![(1 / 1), (1 / 1), (1 / 1)] : Fin 3 → ℝ) (![(z 3 - (-10833981 / 62500000)), (z 15 - (1 / 1)), (z 12 - (226612331 / 500000000))] : Fin 3 → ℝ) (![(z 6 - (-47361589 / 1000000000)), (z 20 - (-639940483 / 500000000)), (z 17 - (226612331 / 500000000))] : Fin 3 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 1
    · exact hz 3
    · exact hz 6
    · exact hz 12
    · exact hz 15
    · exact hz 17
    · exact hz 20)
    (by
    intro i
    fin_cases i
    · exact hz 3
    · exact hz 15
    · exact hz 12)
    (by
    intro i
    fin_cases i
    · exact hz 6
    · exact hz 20
    · exact hz 17)
  have hx : (inactiveExpr 68).eval z = (500000000032676797 / 250000000000000000) + (∑ i, (![(1 / 1), (-47361589 / 1000000000), (-10833981 / 62500000), (226612331 / 500000000), (-639940483 / 500000000), (226612331 / 500000000), (1 / 1)] : Fin 7 → ℝ) i * (![(z 1 - (2066258539 / 1000000000)), (z 3 - (-10833981 / 62500000)), (z 6 - (-47361589 / 1000000000)), (z 12 - (226612331 / 500000000)), (z 15 - (1 / 1)), (z 17 - (226612331 / 500000000)), (z 20 - (-639940483 / 500000000))] : Fin 7 → ℝ) i) + (∑ i, (![(1 / 1), (1 / 1), (1 / 1)] : Fin 3 → ℝ) i * (![(z 3 - (-10833981 / 62500000)), (z 15 - (1 / 1)), (z 12 - (226612331 / 500000000))] : Fin 3 → ℝ) i * (![(z 6 - (-47361589 / 1000000000)), (z 20 - (-639940483 / 500000000)), (z 17 - (226612331 / 500000000))] : Fin 3 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (500000000032676797 / 250000000000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(1 / 1), (-47361589 / 1000000000), (-10833981 / 62500000), (226612331 / 500000000), (-639940483 / 500000000), (226612331 / 500000000), (1 / 1)] : Fin 7 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(1 / 1), (1 / 1), (1 / 1)] : Fin 3 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
