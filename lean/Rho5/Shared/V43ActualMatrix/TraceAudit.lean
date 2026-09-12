import Rho5.Shared.V43ActualMatrix.Trace

/-! D103 kernel receipt (stage B, actual trace, growth and `rho5Trace`). -/

namespace Rho5.Shared.V43ActualMatrix

#check @traceValues
#check @traceValues_eq
#check @delta_eq_w_sub_r
#check @leadingTracePos_tail
#check @leadingTracePos_T2
#check @leadingTracePos_S3
#check @leadingTracePos_S4
#check @leadingTracePos_M_steps
#check @leadingTracePos_M
#check @leadingTracePos_M_both
#check @legalTrace_M
#check @M_ne_zero
#check @abs_w_sub_r_eq_height
#check @growthRatio_ge_height
#check @height_le_rho5Trace

#print axioms delta_eq_w_sub_r
#print axioms leadingTracePos_tail
#print axioms leadingTracePos_M_steps
#print axioms leadingTracePos_M
#print axioms leadingTracePos_M_both
#print axioms legalTrace_M
#print axioms M_ne_zero
#print axioms abs_w_sub_r_eq_height
#print axioms growthRatio_ge_height
#print axioms height_le_rho5Trace

end Rho5.Shared.V43ActualMatrix
