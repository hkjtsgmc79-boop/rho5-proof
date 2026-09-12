import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[77] = positive_r.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_77 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 77).eval z := by
  have he : inactiveExpr 77 = (.mul (.const (1 / 1)) (.var 1)) := rfl
  have h := centered_quadratic_lower (2066258539 / 1000000000)
    (![(1 / 1)] : Fin 1 → ℝ) (![(z 1 - (2066258539 / 1000000000))] : Fin 1 → ℝ) (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 1)
    (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i)
  have hx : (inactiveExpr 77).eval z = (2066258539 / 1000000000) + (∑ i, (![(1 / 1)] : Fin 1 → ℝ) i * (![(z 1 - (2066258539 / 1000000000))] : Fin 1 → ℝ) i) + (∑ i, (![] : Fin 0 → ℝ) i * (![] : Fin 0 → ℝ) i * (![] : Fin 0 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (2066258539 / 1000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(1 / 1)] : Fin 1 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![] : Fin 0 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
