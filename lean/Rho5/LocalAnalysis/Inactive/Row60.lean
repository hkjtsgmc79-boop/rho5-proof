import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[60] = D20+.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_60 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 60).eval z := by
  have he : inactiveExpr 60 = (.add (.mul (.const (1 / 1)) (.var 0)) (.mul (.mul (.const (-1 / 1)) (.var 0)) (.var 6))) := rfl
  have h := centered_quadratic_lower (543179622607040777 / 250000000000000000)
    (![(1047361589 / 1000000000), (-518617093 / 250000000)] : Fin 2 → ℝ) (![(z 0 - (518617093 / 250000000)), (z 6 - (-47361589 / 1000000000))] : Fin 2 → ℝ) (![(-1 / 1)] : Fin 1 → ℝ) (![(z 0 - (518617093 / 250000000))] : Fin 1 → ℝ) (![(z 6 - (-47361589 / 1000000000))] : Fin 1 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 0
    · exact hz 6)
    (by
    intro i
    fin_cases i
    · exact hz 0)
    (by
    intro i
    fin_cases i
    · exact hz 6)
  have hx : (inactiveExpr 60).eval z = (543179622607040777 / 250000000000000000) + (∑ i, (![(1047361589 / 1000000000), (-518617093 / 250000000)] : Fin 2 → ℝ) i * (![(z 0 - (518617093 / 250000000)), (z 6 - (-47361589 / 1000000000))] : Fin 2 → ℝ) i) + (∑ i, (![(-1 / 1)] : Fin 1 → ℝ) i * (![(z 0 - (518617093 / 250000000))] : Fin 1 → ℝ) i * (![(z 6 - (-47361589 / 1000000000))] : Fin 1 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (543179622607040777 / 250000000000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(1047361589 / 1000000000), (-518617093 / 250000000)] : Fin 2 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(-1 / 1)] : Fin 1 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
