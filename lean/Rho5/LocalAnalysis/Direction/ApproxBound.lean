import Rho5.LocalAnalysis.Direction.Row00
import Rho5.LocalAnalysis.Direction.Row01
import Rho5.LocalAnalysis.Direction.Row02
import Rho5.LocalAnalysis.Direction.Row03
import Rho5.LocalAnalysis.Direction.Row04
import Rho5.LocalAnalysis.Direction.Row05
import Rho5.LocalAnalysis.Direction.Row06
import Rho5.LocalAnalysis.Direction.Row07
import Rho5.LocalAnalysis.Direction.Row08
import Rho5.LocalAnalysis.Direction.Row09
import Rho5.LocalAnalysis.Direction.Row10
import Rho5.LocalAnalysis.Direction.Row11
import Rho5.LocalAnalysis.Direction.Row12
import Rho5.LocalAnalysis.Direction.Row13
import Rho5.LocalAnalysis.Direction.Row14
import Rho5.LocalAnalysis.Direction.Row15
import Rho5.LocalAnalysis.Direction.Row16
import Rho5.LocalAnalysis.Direction.Row17
import Rho5.LocalAnalysis.Direction.Row18
import Rho5.LocalAnalysis.Direction.Row19
import Rho5.LocalAnalysis.Direction.Row20
namespace Rho5.LocalAnalysis.V43
noncomputable section
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem directionApprox_bound (z : X) (hz : z ∈ cube center radius) :
    ‖directionApprox z‖ ≤ (43 / 20 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 43 / 20)).mpr
  intro i
  fin_cases i
  · simpa only [Real.norm_eq_abs] using directionApprox_row0_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row1_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row2_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row3_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row4_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row5_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row6_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row7_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row8_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row9_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row10_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row11_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row12_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row13_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row14_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row15_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row16_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row17_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row18_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row19_bound z hz
  · simpa only [Real.norm_eq_abs] using directionApprox_row20_bound z hz
end
end Rho5.LocalAnalysis.V43
