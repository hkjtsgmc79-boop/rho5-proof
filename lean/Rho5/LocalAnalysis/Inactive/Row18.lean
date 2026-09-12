import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[18] = O00-.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_18 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 18).eval z := by
  have he : inactiveExpr 18 = (.add (.add (.add (.const (1 / 1)) (.mul (.const (1 / 1)) (.var 0))) (.mul (.mul (.const (1 / 1)) (.var 13)) (.var 19))) (.mul (.mul (.const (1 / 1)) (.var 10)) (.var 16))) := rfl
  have h := centered_quadratic_lower (2967463 / 1600000)
    (![(1 / 1), (-581690673 / 1000000000), (-159528331 / 250000000), (1 / 1), (1 / 1)] : Fin 5 → ℝ) (![(z 0 - (518617093 / 250000000)), (z 10 - (1 / 1)), (z 13 - (1 / 1)), (z 16 - (-581690673 / 1000000000)), (z 19 - (-159528331 / 250000000))] : Fin 5 → ℝ) (![(1 / 1), (1 / 1)] : Fin 2 → ℝ) (![(z 13 - (1 / 1)), (z 10 - (1 / 1))] : Fin 2 → ℝ) (![(z 19 - (-159528331 / 250000000)), (z 16 - (-581690673 / 1000000000))] : Fin 2 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 0
    · exact hz 10
    · exact hz 13
    · exact hz 16
    · exact hz 19)
    (by
    intro i
    fin_cases i
    · exact hz 13
    · exact hz 10)
    (by
    intro i
    fin_cases i
    · exact hz 19
    · exact hz 16)
  have hx : (inactiveExpr 18).eval z = (2967463 / 1600000) + (∑ i, (![(1 / 1), (-581690673 / 1000000000), (-159528331 / 250000000), (1 / 1), (1 / 1)] : Fin 5 → ℝ) i * (![(z 0 - (518617093 / 250000000)), (z 10 - (1 / 1)), (z 13 - (1 / 1)), (z 16 - (-581690673 / 1000000000)), (z 19 - (-159528331 / 250000000))] : Fin 5 → ℝ) i) + (∑ i, (![(1 / 1), (1 / 1)] : Fin 2 → ℝ) i * (![(z 13 - (1 / 1)), (z 10 - (1 / 1))] : Fin 2 → ℝ) i * (![(z 19 - (-159528331 / 250000000)), (z 16 - (-581690673 / 1000000000))] : Fin 2 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (2967463 / 1600000) - (3 / 1000 : ℝ) * (∑ i, |(![(1 / 1), (-581690673 / 1000000000), (-159528331 / 250000000), (1 / 1), (1 / 1)] : Fin 5 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(1 / 1), (1 / 1)] : Fin 2 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
