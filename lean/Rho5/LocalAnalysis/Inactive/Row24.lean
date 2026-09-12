import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[24] = S02+.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_24 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 24).eval z := by
  have he : inactiveExpr 24 = (.add (.add (.mul (.const (1 / 1)) (.var 7)) (.mul (.const (-1 / 1)) (.var 4))) (.mul (.mul (.const (-1 / 1)) (.var 13)) (.var 21))) := rfl
  have h := centered_quadratic_lower (2647929769 / 1000000000)
    (![(-1 / 1), (1 / 1), (-175952653 / 200000000), (-1 / 1)] : Fin 4 → ℝ) (![(z 4 - (-518617093 / 250000000)), (z 7 - (726612331 / 500000000)), (z 13 - (1 / 1)), (z 21 - (175952653 / 200000000))] : Fin 4 → ℝ) (![(-1 / 1)] : Fin 1 → ℝ) (![(z 13 - (1 / 1))] : Fin 1 → ℝ) (![(z 21 - (175952653 / 200000000))] : Fin 1 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 4
    · exact hz 7
    · exact hz 13
    · exact hz 21)
    (by
    intro i
    fin_cases i
    · exact hz 13)
    (by
    intro i
    fin_cases i
    · exact hz 21)
  have hx : (inactiveExpr 24).eval z = (2647929769 / 1000000000) + (∑ i, (![(-1 / 1), (1 / 1), (-175952653 / 200000000), (-1 / 1)] : Fin 4 → ℝ) i * (![(z 4 - (-518617093 / 250000000)), (z 7 - (726612331 / 500000000)), (z 13 - (1 / 1)), (z 21 - (175952653 / 200000000))] : Fin 4 → ℝ) i) + (∑ i, (![(-1 / 1)] : Fin 1 → ℝ) i * (![(z 13 - (1 / 1))] : Fin 1 → ℝ) i * (![(z 21 - (175952653 / 200000000))] : Fin 1 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (2647929769 / 1000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(-1 / 1), (1 / 1), (-175952653 / 200000000), (-1 / 1)] : Fin 4 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(-1 / 1)] : Fin 1 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
