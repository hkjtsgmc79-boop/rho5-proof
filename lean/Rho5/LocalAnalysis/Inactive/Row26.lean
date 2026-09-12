import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[26] = O02+.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_26 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 26).eval z := by
  have he : inactiveExpr 26 = (.add (.add (.add (.const (1 / 1)) (.mul (.const (-1 / 1)) (.var 4))) (.mul (.mul (.const (-1 / 1)) (.var 13)) (.var 21))) (.mul (.mul (.const (-1 / 1)) (.var 10)) (.var 18))) := rfl
  have h := centered_quadratic_lower (2 / 1)
    (![(-1 / 1), (-194705107 / 1000000000), (-175952653 / 200000000), (-1 / 1), (-1 / 1)] : Fin 5 → ℝ) (![(z 4 - (-518617093 / 250000000)), (z 10 - (1 / 1)), (z 13 - (1 / 1)), (z 18 - (194705107 / 1000000000)), (z 21 - (175952653 / 200000000))] : Fin 5 → ℝ) (![(-1 / 1), (-1 / 1)] : Fin 2 → ℝ) (![(z 13 - (1 / 1)), (z 10 - (1 / 1))] : Fin 2 → ℝ) (![(z 21 - (175952653 / 200000000)), (z 18 - (194705107 / 1000000000))] : Fin 2 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 4
    · exact hz 10
    · exact hz 13
    · exact hz 18
    · exact hz 21)
    (by
    intro i
    fin_cases i
    · exact hz 13
    · exact hz 10)
    (by
    intro i
    fin_cases i
    · exact hz 21
    · exact hz 18)
  have hx : (inactiveExpr 26).eval z = (2 / 1) + (∑ i, (![(-1 / 1), (-194705107 / 1000000000), (-175952653 / 200000000), (-1 / 1), (-1 / 1)] : Fin 5 → ℝ) i * (![(z 4 - (-518617093 / 250000000)), (z 10 - (1 / 1)), (z 13 - (1 / 1)), (z 18 - (194705107 / 1000000000)), (z 21 - (175952653 / 200000000))] : Fin 5 → ℝ) i) + (∑ i, (![(-1 / 1), (-1 / 1)] : Fin 2 → ℝ) i * (![(z 13 - (1 / 1)), (z 10 - (1 / 1))] : Fin 2 → ℝ) i * (![(z 21 - (175952653 / 200000000)), (z 18 - (194705107 / 1000000000))] : Fin 2 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (2 / 1) - (3 / 1000 : ℝ) * (∑ i, |(![(-1 / 1), (-194705107 / 1000000000), (-175952653 / 200000000), (-1 / 1), (-1 / 1)] : Fin 5 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(-1 / 1), (-1 / 1)] : Fin 2 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
