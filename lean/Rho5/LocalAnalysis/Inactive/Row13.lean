import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[13] = P0+.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_13 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 13).eval z := by
  have he : inactiveExpr 13 = (.add (.add (.const (1 / 1)) (.mul (.const (-1 / 1)) (.var 19))) (.mul (.mul (.const (-1 / 1)) (.var 9)) (.var 16))) := rfl
  have h := centered_quadratic_lower (1997326229413113941 / 1000000000000000000)
    (![(581690673 / 1000000000), (-617532517 / 1000000000), (-1 / 1)] : Fin 3 → ℝ) (![(z 9 - (617532517 / 1000000000)), (z 16 - (-581690673 / 1000000000)), (z 19 - (-159528331 / 250000000))] : Fin 3 → ℝ) (![(-1 / 1)] : Fin 1 → ℝ) (![(z 9 - (617532517 / 1000000000))] : Fin 1 → ℝ) (![(z 16 - (-581690673 / 1000000000))] : Fin 1 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 9
    · exact hz 16
    · exact hz 19)
    (by
    intro i
    fin_cases i
    · exact hz 9)
    (by
    intro i
    fin_cases i
    · exact hz 16)
  have hx : (inactiveExpr 13).eval z = (1997326229413113941 / 1000000000000000000) + (∑ i, (![(581690673 / 1000000000), (-617532517 / 1000000000), (-1 / 1)] : Fin 3 → ℝ) i * (![(z 9 - (617532517 / 1000000000)), (z 16 - (-581690673 / 1000000000)), (z 19 - (-159528331 / 250000000))] : Fin 3 → ℝ) i) + (∑ i, (![(-1 / 1)] : Fin 1 → ℝ) i * (![(z 9 - (617532517 / 1000000000))] : Fin 1 → ℝ) i * (![(z 16 - (-581690673 / 1000000000))] : Fin 1 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (1997326229413113941 / 1000000000000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(581690673 / 1000000000), (-617532517 / 1000000000), (-1 / 1)] : Fin 3 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(-1 / 1)] : Fin 1 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
