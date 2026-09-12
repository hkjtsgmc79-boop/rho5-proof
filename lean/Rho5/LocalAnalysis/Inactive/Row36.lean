import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[36] = L1-.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_36 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 36).eval z := by
  have he : inactiveExpr 36 = (.add (.add (.const (1 / 1)) (.mul (.mul (.const (1 / 1)) (.var 7)) (.var 14))) (.mul (.mul (.const (-1 / 1)) (.var 8)) (.var 11))) := rfl
  have h := centered_quadratic_lower (163565554631198129 / 100000000000000000)
    (![(194712659 / 200000000), (-194787661 / 250000000), (-1 / 1), (726612331 / 500000000)] : Fin 4 → ℝ) (![(z 7 - (726612331 / 500000000)), (z 8 - (1 / 1)), (z 11 - (194787661 / 250000000)), (z 14 - (194712659 / 200000000))] : Fin 4 → ℝ) (![(1 / 1), (-1 / 1)] : Fin 2 → ℝ) (![(z 7 - (726612331 / 500000000)), (z 8 - (1 / 1))] : Fin 2 → ℝ) (![(z 14 - (194712659 / 200000000)), (z 11 - (194787661 / 250000000))] : Fin 2 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 7
    · exact hz 8
    · exact hz 11
    · exact hz 14)
    (by
    intro i
    fin_cases i
    · exact hz 7
    · exact hz 8)
    (by
    intro i
    fin_cases i
    · exact hz 14
    · exact hz 11)
  have hx : (inactiveExpr 36).eval z = (163565554631198129 / 100000000000000000) + (∑ i, (![(194712659 / 200000000), (-194787661 / 250000000), (-1 / 1), (726612331 / 500000000)] : Fin 4 → ℝ) i * (![(z 7 - (726612331 / 500000000)), (z 8 - (1 / 1)), (z 11 - (194787661 / 250000000)), (z 14 - (194712659 / 200000000))] : Fin 4 → ℝ) i) + (∑ i, (![(1 / 1), (-1 / 1)] : Fin 2 → ℝ) i * (![(z 7 - (726612331 / 500000000)), (z 8 - (1 / 1))] : Fin 2 → ℝ) i * (![(z 14 - (194712659 / 200000000)), (z 11 - (194787661 / 250000000))] : Fin 2 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (163565554631198129 / 100000000000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(194712659 / 200000000), (-194787661 / 250000000), (-1 / 1), (726612331 / 500000000)] : Fin 4 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(1 / 1), (-1 / 1)] : Fin 2 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
