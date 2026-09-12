import Rho5.Algebraic.CandidateBox
import Rho5.ExternalAttainment.Interval

noncomputable section
namespace Rho5.ExternalAttainment

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

/-- A rational outer box for this proof only; the exported theorem takes the
original `Rho5.Algebraic.CandidateBox`, not this auxiliary proposition. -/
structure NarrowBox (x y z g : ℝ) : Prop where
  xb : Bounds ((-617532677:ℝ)/1000000000) ((-617532676:ℝ)/1000000000) x
  yb : Bounds ((-779150743:ℝ)/1000000000) ((-779150742:ℝ)/1000000000) y
  zb : Bounds ((453224909:ℝ)/1000000000) ((453224910:ℝ)/1000000000) z
  gb : Bounds ((4132517078:ℝ)/1000000000) ((4132517079:ℝ)/1000000000) g

theorem narrowBox_of_candidateBox {x y z g : ℝ}
    (h : Rho5.Algebraic.CandidateBox x y z g) : NarrowBox x y z g := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact le_trans (by norm_num [Rho5.Algebraic.xLower]) h.x_lower
  · exact le_trans h.x_upper (by norm_num [Rho5.Algebraic.xUpper])
  · exact le_trans (by norm_num [Rho5.Algebraic.yLower]) h.y_lower
  · exact le_trans h.y_upper (by norm_num [Rho5.Algebraic.yUpper])
  · exact le_trans (by norm_num [Rho5.Algebraic.zLower]) h.z_lower
  · exact le_trans h.z_upper (by norm_num [Rho5.Algebraic.zUpper])
  · exact le_trans (by norm_num [Rho5.Algebraic.gLower]) h.g_lower
  · exact le_trans h.g_upper (by norm_num [Rho5.Algebraic.gUpper])

theorem candidate_g_gt_four {x y z g : ℝ}
    (h : Rho5.Algebraic.CandidateBox x y z g) : 4 < g := by
  have hb := (narrowBox_of_candidateBox h).gb
  linarith [hb.1]

end Rho5.ExternalAttainment
