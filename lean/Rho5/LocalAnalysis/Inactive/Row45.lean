import Rho5.LocalAnalysis.QuadraticBounds
import Rho5.LocalAnalysis.PhysicalCover

-- Frozen V43 case 0 replacement chart, inactive[45] = O11-.
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

theorem inactive_45 (z : X) (hz : z ∈ cube center radius) :
    (1 / 200 : ℝ) < (inactiveExpr 45).eval z := by
  have he : inactiveExpr 45 = (.add (.add (.add (.add (.const (1 / 1)) (.mul (.const (1 / 1)) (.var 1))) (.mul (.mul (.const (1 / 1)) (.var 3)) (.var 5))) (.mul (.mul (.const (1 / 1)) (.var 14)) (.var 20))) (.mul (.mul (.const (1 / 1)) (.var 11)) (.var 17))) := rfl
  have h := centered_quadratic_lower (999999999903619679 / 500000000000000000)
    (![(1 / 1), (1 / 1), (-10833981 / 62500000), (226612331 / 500000000), (-639940483 / 500000000), (194787661 / 250000000), (194712659 / 200000000)] : Fin 7 → ℝ) (![(z 1 - (2066258539 / 1000000000)), (z 3 - (-10833981 / 62500000)), (z 5 - (1 / 1)), (z 11 - (194787661 / 250000000)), (z 14 - (194712659 / 200000000)), (z 17 - (226612331 / 500000000)), (z 20 - (-639940483 / 500000000))] : Fin 7 → ℝ) (![(1 / 1), (1 / 1), (1 / 1)] : Fin 3 → ℝ) (![(z 3 - (-10833981 / 62500000)), (z 14 - (194712659 / 200000000)), (z 11 - (194787661 / 250000000))] : Fin 3 → ℝ) (![(z 5 - (1 / 1)), (z 20 - (-639940483 / 500000000)), (z 17 - (226612331 / 500000000))] : Fin 3 → ℝ)
    (ρ := (3 / 1000 : ℝ)) (by norm_num)
    (by
    intro i
    fin_cases i
    · exact hz 1
    · exact hz 3
    · exact hz 5
    · exact hz 11
    · exact hz 14
    · exact hz 17
    · exact hz 20)
    (by
    intro i
    fin_cases i
    · exact hz 3
    · exact hz 14
    · exact hz 11)
    (by
    intro i
    fin_cases i
    · exact hz 5
    · exact hz 20
    · exact hz 17)
  have hx : (inactiveExpr 45).eval z = (999999999903619679 / 500000000000000000) + (∑ i, (![(1 / 1), (1 / 1), (-10833981 / 62500000), (226612331 / 500000000), (-639940483 / 500000000), (194787661 / 250000000), (194712659 / 200000000)] : Fin 7 → ℝ) i * (![(z 1 - (2066258539 / 1000000000)), (z 3 - (-10833981 / 62500000)), (z 5 - (1 / 1)), (z 11 - (194787661 / 250000000)), (z 14 - (194712659 / 200000000)), (z 17 - (226612331 / 500000000)), (z 20 - (-639940483 / 500000000))] : Fin 7 → ℝ) i) + (∑ i, (![(1 / 1), (1 / 1), (1 / 1)] : Fin 3 → ℝ) i * (![(z 3 - (-10833981 / 62500000)), (z 14 - (194712659 / 200000000)), (z 11 - (194787661 / 250000000))] : Fin 3 → ℝ) i * (![(z 5 - (1 / 1)), (z 20 - (-639940483 / 500000000)), (z 17 - (226612331 / 500000000))] : Fin 3 → ℝ) i) := by
    rw [he]
    norm_num [Expr.eval, Fin.sum_univ_succ] <;> ring
  rw [← hx] at h
  have hl : (1 / 200 : ℝ) <
      (999999999903619679 / 500000000000000000) - (3 / 1000 : ℝ) * (∑ i, |(![(1 / 1), (1 / 1), (-10833981 / 62500000), (226612331 / 500000000), (-639940483 / 500000000), (194787661 / 250000000), (194712659 / 200000000)] : Fin 7 → ℝ) i|) -
        (3 / 1000 : ℝ) ^ 2 * (∑ i, |(![(1 / 1), (1 / 1), (1 / 1)] : Fin 3 → ℝ) i|) := by
    norm_num [Fin.sum_univ_succ]
  exact hl.trans_le h

end
end Rho5.LocalAnalysis.V43
