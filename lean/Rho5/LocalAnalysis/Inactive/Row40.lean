import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[40] = O10-.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_40 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 40).eval z := by
  have he : inactiveExpr 40 = (.add (.add (.add (.const (1 / 1)) (.mul (.mul (.const (1 / 1)) (.var 0)) (.var 5))) (.mul (.mul (.const (1 / 1)) (.var 14)) (.var 19))) (.mul (.mul (.const (1 / 1)) (.var 11)) (.var 16))) := rfl
  have h := centered_quadratic_lower (249999999903301751 / 125000000000000000)
    (![(1 / 1), (518617093 / 250000000), (-581690673 / 1000000000), (-159528331 / 250000000), (194787661 / 250000000), (194712659 / 200000000)] : Fin 6 → ℝ) (![(z 0 - (518617093 / 250000000)), (z 5 - (1 / 1)), (z 11 - (194787661 / 250000000)), (z 14 - (194712659 / 200000000)), (z 16 - (-581690673 / 1000000000)), (z 19 - (-159528331 / 250000000))] : Fin 6 → ℝ) (![(1 / 1), (1 / 1), (1 / 1)] : Fin 3 → ℝ) (![(z 0 - (518617093 / 250000000)), (z 14 - (194712659 / 200000000)), (z 11 - (194787661 / 250000000))] : Fin 3 → ℝ) (![(z 5 - (1 / 1)), (z 19 - (-159528331 / 250000000)), (z 16 - (-581690673 / 1000000000))] : Fin 3 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 0
    · exact hz 5
    · exact hz 11
    · exact hz 14
    · exact hz 16
    · exact hz 19)
    (by
    intro i
    fin_cases i
    · exact hz 0
    · exact hz 14
    · exact hz 11)
    (by
    intro i
    fin_cases i
    · exact hz 5
    · exact hz 19
    · exact hz 16)
  have hx : (inactiveExpr 40).eval z = (249999999903301751 / 125000000000000000) + (∑ i, (![(1 / 1), (518617093 / 250000000), (-581690673 / 1000000000), (-159528331 / 250000000), (194787661 / 250000000), (194712659 / 200000000)] : Fin 6 → ℝ) i * (![(z 0 - (518617093 / 250000000)), (z 5 - (1 / 1)), (z 11 - (194787661 / 250000000)), (z 14 - (194712659 / 200000000)), (z 16 - (-581690673 / 1000000000)), (z 19 - (-159528331 / 250000000))] : Fin 6 → ℝ) i) + (∑ i, (![(1 / 1), (1 / 1), (1 / 1)] : Fin 3 → ℝ) i * (![(z 0 - (518617093 / 250000000)), (z 14 - (194712659 / 200000000)), (z 11 - (194787661 / 250000000))] : Fin 3 → ℝ) i * (![(z 5 - (1 / 1)), (z 19 - (-159528331 / 250000000)), (z 16 - (-581690673 / 1000000000))] : Fin 3 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (249999999903301751 / 125000000000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(1 / 1), (518617093 / 250000000), (-581690673 / 1000000000), (-159528331 / 250000000), (194787661 / 250000000), (194712659 / 200000000)] : Fin 6 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(1 / 1), (1 / 1), (1 / 1)] : Fin 3 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
