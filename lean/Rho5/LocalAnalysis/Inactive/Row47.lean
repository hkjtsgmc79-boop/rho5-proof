import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[47] = D12-.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_47 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 47).eval z := by
  have he : inactiveExpr 47 = (.add (.add (.mul (.const (1 / 1)) (.var 0)) (.mul (.const (1 / 1)) (.var 1))) (.mul (.mul (.const (1 / 1)) (.var 4)) (.var 5))) := rfl
  have h := centered_quadratic_lower (2066258539 / 1000000000)
    (![(1 / 1), (1 / 1), (1 / 1), (-518617093 / 250000000)] : Fin 4 → ℝ) (![(z 0 - (518617093 / 250000000)), (z 1 - (2066258539 / 1000000000)), (z 4 - (-518617093 / 250000000)), (z 5 - (1 / 1))] : Fin 4 → ℝ) (![(1 / 1)] : Fin 1 → ℝ) (![(z 4 - (-518617093 / 250000000))] : Fin 1 → ℝ) (![(z 5 - (1 / 1))] : Fin 1 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 0
    · exact hz 1
    · exact hz 4
    · exact hz 5)
    (by
    intro i
    fin_cases i
    · exact hz 4)
    (by
    intro i
    fin_cases i
    · exact hz 5)
  have hx : (inactiveExpr 47).eval z = (2066258539 / 1000000000) + (∑ i, (![(1 / 1), (1 / 1), (1 / 1), (-518617093 / 250000000)] : Fin 4 → ℝ) i * (![(z 0 - (518617093 / 250000000)), (z 1 - (2066258539 / 1000000000)), (z 4 - (-518617093 / 250000000)), (z 5 - (1 / 1))] : Fin 4 → ℝ) i) + (∑ i, (![(1 / 1)] : Fin 1 → ℝ) i * (![(z 4 - (-518617093 / 250000000))] : Fin 1 → ℝ) i * (![(z 5 - (1 / 1))] : Fin 1 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (2066258539 / 1000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(1 / 1), (1 / 1), (1 / 1), (-518617093 / 250000000)] : Fin 4 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(1 / 1)] : Fin 1 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
