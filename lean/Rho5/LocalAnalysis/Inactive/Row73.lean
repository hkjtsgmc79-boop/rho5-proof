import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[73] = O22+.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_73 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 73).eval z := by
  have he : inactiveExpr 73 = (.add (.add (.add (.add (.const (1 / 1)) (.mul (.const (-1 / 1)) (.var 2))) (.mul (.mul (.const (-1 / 1)) (.var 4)) (.var 6))) (.mul (.mul (.const (-1 / 1)) (.var 15)) (.var 21))) (.mul (.mul (.const (-1 / 1)) (.var 12)) (.var 18))) := rfl
  have h := centered_quadratic_lower (999999999631044029 / 500000000000000000)
    (![(-1 / 1), (47361589 / 1000000000), (518617093 / 250000000), (-194705107 / 1000000000), (-175952653 / 200000000), (-226612331 / 500000000), (-1 / 1)] : Fin 7 → ℝ) (![(z 2 - (-2066258539 / 1000000000)), (z 4 - (-518617093 / 250000000)), (z 6 - (-47361589 / 1000000000)), (z 12 - (226612331 / 500000000)), (z 15 - (1 / 1)), (z 18 - (194705107 / 1000000000)), (z 21 - (175952653 / 200000000))] : Fin 7 → ℝ) (![(-1 / 1), (-1 / 1), (-1 / 1)] : Fin 3 → ℝ) (![(z 4 - (-518617093 / 250000000)), (z 15 - (1 / 1)), (z 12 - (226612331 / 500000000))] : Fin 3 → ℝ) (![(z 6 - (-47361589 / 1000000000)), (z 21 - (175952653 / 200000000)), (z 18 - (194705107 / 1000000000))] : Fin 3 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 2
    · exact hz 4
    · exact hz 6
    · exact hz 12
    · exact hz 15
    · exact hz 18
    · exact hz 21)
    (by
    intro i
    fin_cases i
    · exact hz 4
    · exact hz 15
    · exact hz 12)
    (by
    intro i
    fin_cases i
    · exact hz 6
    · exact hz 21
    · exact hz 18)
  have hx : (inactiveExpr 73).eval z = (999999999631044029 / 500000000000000000) + (∑ i, (![(-1 / 1), (47361589 / 1000000000), (518617093 / 250000000), (-194705107 / 1000000000), (-175952653 / 200000000), (-226612331 / 500000000), (-1 / 1)] : Fin 7 → ℝ) i * (![(z 2 - (-2066258539 / 1000000000)), (z 4 - (-518617093 / 250000000)), (z 6 - (-47361589 / 1000000000)), (z 12 - (226612331 / 500000000)), (z 15 - (1 / 1)), (z 18 - (194705107 / 1000000000)), (z 21 - (175952653 / 200000000))] : Fin 7 → ℝ) i) + (∑ i, (![(-1 / 1), (-1 / 1), (-1 / 1)] : Fin 3 → ℝ) i * (![(z 4 - (-518617093 / 250000000)), (z 15 - (1 / 1)), (z 12 - (226612331 / 500000000))] : Fin 3 → ℝ) i * (![(z 6 - (-47361589 / 1000000000)), (z 21 - (175952653 / 200000000)), (z 18 - (194705107 / 1000000000))] : Fin 3 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (999999999631044029 / 500000000000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(-1 / 1), (47361589 / 1000000000), (518617093 / 250000000), (-194705107 / 1000000000), (-175952653 / 200000000), (-226612331 / 500000000), (-1 / 1)] : Fin 7 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(-1 / 1), (-1 / 1), (-1 / 1)] : Fin 3 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
