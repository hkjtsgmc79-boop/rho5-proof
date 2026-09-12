import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[66] = S21+.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_66 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 66).eval z := by
  have he : inactiveExpr 66 = (.add (.add (.add (.mul (.const (1 / 1)) (.var 7)) (.mul (.const (-1 / 1)) (.var 1))) (.mul (.mul (.const (-1 / 1)) (.var 3)) (.var 6))) (.mul (.mul (.const (-1 / 1)) (.var 15)) (.var 20))) := rfl
  have h := centered_quadratic_lower (41164828507144191 / 62500000000000000)
    (![(-1 / 1), (47361589 / 1000000000), (10833981 / 62500000), (1 / 1), (639940483 / 500000000), (-1 / 1)] : Fin 6 → ℝ) (![(z 1 - (2066258539 / 1000000000)), (z 3 - (-10833981 / 62500000)), (z 6 - (-47361589 / 1000000000)), (z 7 - (726612331 / 500000000)), (z 15 - (1 / 1)), (z 20 - (-639940483 / 500000000))] : Fin 6 → ℝ) (![(-1 / 1), (-1 / 1)] : Fin 2 → ℝ) (![(z 3 - (-10833981 / 62500000)), (z 15 - (1 / 1))] : Fin 2 → ℝ) (![(z 6 - (-47361589 / 1000000000)), (z 20 - (-639940483 / 500000000))] : Fin 2 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 1
    · exact hz 3
    · exact hz 6
    · exact hz 7
    · exact hz 15
    · exact hz 20)
    (by
    intro i
    fin_cases i
    · exact hz 3
    · exact hz 15)
    (by
    intro i
    fin_cases i
    · exact hz 6
    · exact hz 20)
  have hx : (inactiveExpr 66).eval z = (41164828507144191 / 62500000000000000) + (∑ i, (![(-1 / 1), (47361589 / 1000000000), (10833981 / 62500000), (1 / 1), (639940483 / 500000000), (-1 / 1)] : Fin 6 → ℝ) i * (![(z 1 - (2066258539 / 1000000000)), (z 3 - (-10833981 / 62500000)), (z 6 - (-47361589 / 1000000000)), (z 7 - (726612331 / 500000000)), (z 15 - (1 / 1)), (z 20 - (-639940483 / 500000000))] : Fin 6 → ℝ) i) + (∑ i, (![(-1 / 1), (-1 / 1)] : Fin 2 → ℝ) i * (![(z 3 - (-10833981 / 62500000)), (z 15 - (1 / 1))] : Fin 2 → ℝ) i * (![(z 6 - (-47361589 / 1000000000)), (z 20 - (-639940483 / 500000000))] : Fin 2 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (41164828507144191 / 62500000000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(-1 / 1), (47361589 / 1000000000), (10833981 / 62500000), (1 / 1), (639940483 / 500000000), (-1 / 1)] : Fin 6 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(-1 / 1), (-1 / 1)] : Fin 2 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
