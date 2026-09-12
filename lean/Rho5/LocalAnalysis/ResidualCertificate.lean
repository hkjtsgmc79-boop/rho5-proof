import Rho5.LocalAnalysis.ResidualRows.Row00
import Rho5.LocalAnalysis.ResidualRows.Row01
import Rho5.LocalAnalysis.ResidualRows.Row02
import Rho5.LocalAnalysis.ResidualRows.Row03
import Rho5.LocalAnalysis.ResidualRows.Row04
import Rho5.LocalAnalysis.ResidualRows.Row05
import Rho5.LocalAnalysis.ResidualRows.Row06
import Rho5.LocalAnalysis.ResidualRows.Row07
import Rho5.LocalAnalysis.ResidualRows.Row08
import Rho5.LocalAnalysis.ResidualRows.Row09
import Rho5.LocalAnalysis.ResidualRows.Row10
import Rho5.LocalAnalysis.ResidualRows.Row11
import Rho5.LocalAnalysis.ResidualRows.Row12
import Rho5.LocalAnalysis.ResidualRows.Row13
import Rho5.LocalAnalysis.ResidualRows.Row14
import Rho5.LocalAnalysis.ResidualRows.Row15
import Rho5.LocalAnalysis.ResidualRows.Row16
import Rho5.LocalAnalysis.ResidualRows.Row17
import Rho5.LocalAnalysis.ResidualRows.Row18
import Rho5.LocalAnalysis.ResidualRows.Row19
import Rho5.LocalAnalysis.ResidualRows.Row20
namespace Rho5.LocalAnalysis.V43
noncomputable section
/-- Actual complete 21×21 whole-cube semantic residual bound. -/
theorem wholeBoxResidual_checked : WholeBoxResidual := by
  intro z hz v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg qBound_nonneg (norm_nonneg v))).mpr
  intro i
  fin_cases i
  · simpa only [Real.norm_eq_abs] using residualRow0_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow1_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow2_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow3_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow4_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow5_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow6_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow7_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow8_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow9_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow10_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow11_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow12_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow13_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow14_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow15_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow16_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow17_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow18_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow19_bound z hz v
  · simpa only [Real.norm_eq_abs] using residualRow20_bound z hz v

theorem actual_jacobian_bijective (z : X) (hz : z ∈ cube center radius) :
    Function.Bijective (jacobian z) := wholeBox_inverse wholeBoxResidual_checked z hz

theorem actual_inverse_direction (z : X) (hz : z ∈ cube center radius) (b : Y) :
    ∃! v : Y, jacobian z v = b ∧ ‖v‖ ≤ ‖preconditioner b‖ / (1 - qBound) :=
  wholeBox_direction wholeBoxResidual_checked z hz b
#print axioms wholeBoxResidual_checked
#print axioms actual_inverse_direction
end
end Rho5.LocalAnalysis.V43
