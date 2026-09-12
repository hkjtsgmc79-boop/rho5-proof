import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[4] = head-.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_04 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 4).eval z := by
  have he : inactiveExpr 4 = (.add (.add (.const (1 / 1)) (.mul (.const (1 / 1)) (.var 7))) (.mul (.mul (.const (-1 / 1)) (.var 8)) (.var 9))) := rfl
  have h := centered_quadratic_lower (367138429 / 200000000)
    (![(1 / 1), (-617532517 / 1000000000), (-1 / 1)] : Fin 3 → ℝ) (![(z 7 - (726612331 / 500000000)), (z 8 - (1 / 1)), (z 9 - (617532517 / 1000000000))] : Fin 3 → ℝ) (![(-1 / 1)] : Fin 1 → ℝ) (![(z 8 - (1 / 1))] : Fin 1 → ℝ) (![(z 9 - (617532517 / 1000000000))] : Fin 1 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 7
    · exact hz 8
    · exact hz 9)
    (by
    intro i
    fin_cases i
    · exact hz 8)
    (by
    intro i
    fin_cases i
    · exact hz 9)
  have hx : (inactiveExpr 4).eval z = (367138429 / 200000000) + (∑ i, (![(1 / 1), (-617532517 / 1000000000), (-1 / 1)] : Fin 3 → ℝ) i * (![(z 7 - (726612331 / 500000000)), (z 8 - (1 / 1)), (z 9 - (617532517 / 1000000000))] : Fin 3 → ℝ) i) + (∑ i, (![(-1 / 1)] : Fin 1 → ℝ) i * (![(z 8 - (1 / 1))] : Fin 1 → ℝ) i * (![(z 9 - (617532517 / 1000000000))] : Fin 1 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (367138429 / 200000000) - (3 / 1000 : ℝ) * (∑ i, |(![(1 / 1), (-617532517 / 1000000000), (-1 / 1)] : Fin 3 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(-1 / 1)] : Fin 1 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
