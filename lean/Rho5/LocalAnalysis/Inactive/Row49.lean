import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[49] = S12-.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_49 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 49).eval z := by
  have he : inactiveExpr 49 = (.add (.add (.add (.mul (.const (1 / 1)) (.var 7)) (.mul (.const (1 / 1)) (.var 1))) (.mul (.mul (.const (1 / 1)) (.var 4)) (.var 5))) (.mul (.mul (.const (1 / 1)) (.var 14)) (.var 21))) := rfl
  have h := centered_quadratic_lower (92060802083734327 / 40000000000000000)
    (![(1 / 1), (1 / 1), (-518617093 / 250000000), (1 / 1), (175952653 / 200000000), (194712659 / 200000000)] : Fin 6 → ℝ) (![(z 1 - (2066258539 / 1000000000)), (z 4 - (-518617093 / 250000000)), (z 5 - (1 / 1)), (z 7 - (726612331 / 500000000)), (z 14 - (194712659 / 200000000)), (z 21 - (175952653 / 200000000))] : Fin 6 → ℝ) (![(1 / 1), (1 / 1)] : Fin 2 → ℝ) (![(z 4 - (-518617093 / 250000000)), (z 14 - (194712659 / 200000000))] : Fin 2 → ℝ) (![(z 5 - (1 / 1)), (z 21 - (175952653 / 200000000))] : Fin 2 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 1
    · exact hz 4
    · exact hz 5
    · exact hz 7
    · exact hz 14
    · exact hz 21)
    (by
    intro i
    fin_cases i
    · exact hz 4
    · exact hz 14)
    (by
    intro i
    fin_cases i
    · exact hz 5
    · exact hz 21)
  have hx : (inactiveExpr 49).eval z = (92060802083734327 / 40000000000000000) + (∑ i, (![(1 / 1), (1 / 1), (-518617093 / 250000000), (1 / 1), (175952653 / 200000000), (194712659 / 200000000)] : Fin 6 → ℝ) i * (![(z 1 - (2066258539 / 1000000000)), (z 4 - (-518617093 / 250000000)), (z 5 - (1 / 1)), (z 7 - (726612331 / 500000000)), (z 14 - (194712659 / 200000000)), (z 21 - (175952653 / 200000000))] : Fin 6 → ℝ) i) + (∑ i, (![(1 / 1), (1 / 1)] : Fin 2 → ℝ) i * (![(z 4 - (-518617093 / 250000000)), (z 14 - (194712659 / 200000000))] : Fin 2 → ℝ) i * (![(z 5 - (1 / 1)), (z 21 - (175952653 / 200000000))] : Fin 2 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (92060802083734327 / 40000000000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(1 / 1), (1 / 1), (-518617093 / 250000000), (1 / 1), (175952653 / 200000000), (194712659 / 200000000)] : Fin 6 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(1 / 1), (1 / 1)] : Fin 2 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
