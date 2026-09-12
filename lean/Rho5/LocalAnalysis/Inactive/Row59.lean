import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[59] = P2-.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_59 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 59).eval z := by
  have he : inactiveExpr 59 = (.add (.add (.const (1 / 1)) (.mul (.const (1 / 1)) (.var 21))) (.mul (.mul (.const (1 / 1)) (.var 9)) (.var 18))) := rfl
  have h := centered_quadratic_lower (1999999999798464319 / 1000000000000000000)
    (![(194705107 / 1000000000), (617532517 / 1000000000), (1 / 1)] : Fin 3 → ℝ) (![(z 9 - (617532517 / 1000000000)), (z 18 - (194705107 / 1000000000)), (z 21 - (175952653 / 200000000))] : Fin 3 → ℝ) (![(1 / 1)] : Fin 1 → ℝ) (![(z 9 - (617532517 / 1000000000))] : Fin 1 → ℝ) (![(z 18 - (194705107 / 1000000000))] : Fin 1 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 9
    · exact hz 18
    · exact hz 21)
    (by
    intro i
    fin_cases i
    · exact hz 9)
    (by
    intro i
    fin_cases i
    · exact hz 18)
  have hx : (inactiveExpr 59).eval z = (1999999999798464319 / 1000000000000000000) + (∑ i, (![(194705107 / 1000000000), (617532517 / 1000000000), (1 / 1)] : Fin 3 → ℝ) i * (![(z 9 - (617532517 / 1000000000)), (z 18 - (194705107 / 1000000000)), (z 21 - (175952653 / 200000000))] : Fin 3 → ℝ) i) + (∑ i, (![(1 / 1)] : Fin 1 → ℝ) i * (![(z 9 - (617532517 / 1000000000))] : Fin 1 → ℝ) i * (![(z 18 - (194705107 / 1000000000))] : Fin 1 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (1999999999798464319 / 1000000000000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(194705107 / 1000000000), (617532517 / 1000000000), (1 / 1)] : Fin 3 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(1 / 1)] : Fin 1 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
