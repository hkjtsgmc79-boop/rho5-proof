import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[50] = O12-.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_50 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 50).eval z := by
  have he : inactiveExpr 50 = (.add (.add (.add (.add (.const (1 / 1)) (.mul (.const (1 / 1)) (.var 1))) (.mul (.mul (.const (1 / 1)) (.var 4)) (.var 5))) (.mul (.mul (.const (1 / 1)) (.var 14)) (.var 21))) (.mul (.mul (.const (1 / 1)) (.var 11)) (.var 18))) := rfl
  have h := centered_quadratic_lower (1999999999602497083 / 1000000000000000000)
    (![(1 / 1), (1 / 1), (-518617093 / 250000000), (194705107 / 1000000000), (175952653 / 200000000), (194787661 / 250000000), (194712659 / 200000000)] : Fin 7 → ℝ) (![(z 1 - (2066258539 / 1000000000)), (z 4 - (-518617093 / 250000000)), (z 5 - (1 / 1)), (z 11 - (194787661 / 250000000)), (z 14 - (194712659 / 200000000)), (z 18 - (194705107 / 1000000000)), (z 21 - (175952653 / 200000000))] : Fin 7 → ℝ) (![(1 / 1), (1 / 1), (1 / 1)] : Fin 3 → ℝ) (![(z 4 - (-518617093 / 250000000)), (z 14 - (194712659 / 200000000)), (z 11 - (194787661 / 250000000))] : Fin 3 → ℝ) (![(z 5 - (1 / 1)), (z 21 - (175952653 / 200000000)), (z 18 - (194705107 / 1000000000))] : Fin 3 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 1
    · exact hz 4
    · exact hz 5
    · exact hz 11
    · exact hz 14
    · exact hz 18
    · exact hz 21)
    (by
    intro i
    fin_cases i
    · exact hz 4
    · exact hz 14
    · exact hz 11)
    (by
    intro i
    fin_cases i
    · exact hz 5
    · exact hz 21
    · exact hz 18)
  have hx : (inactiveExpr 50).eval z = (1999999999602497083 / 1000000000000000000) + (∑ i, (![(1 / 1), (1 / 1), (-518617093 / 250000000), (194705107 / 1000000000), (175952653 / 200000000), (194787661 / 250000000), (194712659 / 200000000)] : Fin 7 → ℝ) i * (![(z 1 - (2066258539 / 1000000000)), (z 4 - (-518617093 / 250000000)), (z 5 - (1 / 1)), (z 11 - (194787661 / 250000000)), (z 14 - (194712659 / 200000000)), (z 18 - (194705107 / 1000000000)), (z 21 - (175952653 / 200000000))] : Fin 7 → ℝ) i) + (∑ i, (![(1 / 1), (1 / 1), (1 / 1)] : Fin 3 → ℝ) i * (![(z 4 - (-518617093 / 250000000)), (z 14 - (194712659 / 200000000)), (z 11 - (194787661 / 250000000))] : Fin 3 → ℝ) i * (![(z 5 - (1 / 1)), (z 21 - (175952653 / 200000000)), (z 18 - (194705107 / 1000000000))] : Fin 3 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (1999999999602497083 / 1000000000000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(1 / 1), (1 / 1), (-518617093 / 250000000), (194705107 / 1000000000), (175952653 / 200000000), (194787661 / 250000000), (194712659 / 200000000)] : Fin 7 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(1 / 1), (1 / 1), (1 / 1)] : Fin 3 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
