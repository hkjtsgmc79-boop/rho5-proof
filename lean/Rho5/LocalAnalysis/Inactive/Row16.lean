import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[16] = S00-.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_16 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 16).eval z := by
  have he : inactiveExpr 16 = (.add (.add (.mul (.const (1 / 1)) (.var 7)) (.mul (.const (1 / 1)) (.var 0))) (.mul (.mul (.const (1 / 1)) (.var 13)) (.var 19))) := rfl
  have h := centered_quadratic_lower (288957971 / 100000000)
    (![(1 / 1), (1 / 1), (-159528331 / 250000000), (1 / 1)] : Fin 4 → ℝ) (![(z 0 - (518617093 / 250000000)), (z 7 - (726612331 / 500000000)), (z 13 - (1 / 1)), (z 19 - (-159528331 / 250000000))] : Fin 4 → ℝ) (![(1 / 1)] : Fin 1 → ℝ) (![(z 13 - (1 / 1))] : Fin 1 → ℝ) (![(z 19 - (-159528331 / 250000000))] : Fin 1 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 0
    · exact hz 7
    · exact hz 13
    · exact hz 19)
    (by
    intro i
    fin_cases i
    · exact hz 13)
    (by
    intro i
    fin_cases i
    · exact hz 19)
  have hx : (inactiveExpr 16).eval z = (288957971 / 100000000) + (∑ i, (![(1 / 1), (1 / 1), (-159528331 / 250000000), (1 / 1)] : Fin 4 → ℝ) i * (![(z 0 - (518617093 / 250000000)), (z 7 - (726612331 / 500000000)), (z 13 - (1 / 1)), (z 19 - (-159528331 / 250000000))] : Fin 4 → ℝ) i) + (∑ i, (![(1 / 1)] : Fin 1 → ℝ) i * (![(z 13 - (1 / 1))] : Fin 1 → ℝ) i * (![(z 19 - (-159528331 / 250000000))] : Fin 1 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (288957971 / 100000000) - (3 / 1000 : ℝ) * (∑ i, |(![(1 / 1), (1 / 1), (-159528331 / 250000000), (1 / 1)] : Fin 4 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(1 / 1)] : Fin 1 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
