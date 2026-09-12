import Rho5.Shared.LastThreePivotEnvelope.StageA
import Rho5.Shared.LastThreePivotEnvelope.GlobalBound

/-! D87 阶段 A（实际最后三阶包络）与阶段 B（全局 `rho5Trace ≤ 81/16`）的具名审计命令
（是命令，不是预先写好的审计结论；必须真的跑 Lean）。

`#print` 给出完整定理类型（`pp.proofs false` 只压掉证明项，不压类型），
`#print axioms` 只列具名公理，二者都在本 lane 的真实成功日志里。 -/
set_option pp.proofs false

/-! ## 实际 Schur 链与冻结固定顺序更新一致 -/

#print Rho5.LastThreePivotEnvelope.S4_eq_fixedSchur
#print axioms Rho5.LastThreePivotEnvelope.S4_eq_fixedSchur

#print Rho5.LastThreePivotEnvelope.S3_eq_fixedSchur
#print axioms Rho5.LastThreePivotEnvelope.S3_eq_fixedSchur

#print Rho5.LastThreePivotEnvelope.T2_eq_fixedSchur
#print axioms Rho5.LastThreePivotEnvelope.T2_eq_fixedSchur

#print Rho5.LastThreePivotEnvelope.delta_eq_fixedSchur
#print axioms Rho5.LastThreePivotEnvelope.delta_eq_fixedSchur

/-! ## 归一化块的条目与主元读数 -/

#print Rho5.LastThreePivotEnvelope.scaledS3_apply
#print axioms Rho5.LastThreePivotEnvelope.scaledS3_apply

#print Rho5.LastThreePivotEnvelope.scaledS3_zero_zero
#print axioms Rho5.LastThreePivotEnvelope.scaledS3_zero_zero

#print Rho5.LastThreePivotEnvelope.abs_scaledS3_le_one
#print axioms Rho5.LastThreePivotEnvelope.abs_scaledS3_le_one

#print Rho5.LastThreePivotEnvelope.scaledS3_fixedSchur
#print axioms Rho5.LastThreePivotEnvelope.scaledS3_fixedSchur

#print Rho5.LastThreePivotEnvelope.scaledS3_fixedSchur_fixedSchur
#print axioms Rho5.LastThreePivotEnvelope.scaledS3_fixedSchur_fixedSchur

#print Rho5.LastThreePivotEnvelope.secondMagnitude_scaledS3
#print axioms Rho5.LastThreePivotEnvelope.secondMagnitude_scaledS3

#print Rho5.LastThreePivotEnvelope.thirdMagnitude_scaledS3
#print axioms Rho5.LastThreePivotEnvelope.thirdMagnitude_scaledS3

/-! ## `A3` 满足 D83 的输入结构与两条实际包络 -/

#print Rho5.LastThreePivotEnvelope.fixedOrderNormalized3_scaledS3
#print axioms Rho5.LastThreePivotEnvelope.fixedOrderNormalized3_scaledS3

#print Rho5.LastThreePivotEnvelope.delta_abs_le_k_mul_phi
#print axioms Rho5.LastThreePivotEnvelope.delta_abs_le_k_mul_phi

#print Rho5.LastThreePivotEnvelope.delta_abs_le_nine_quarters_mul_k
#print axioms Rho5.LastThreePivotEnvelope.delta_abs_le_nine_quarters_mul_k

#print Rho5.LastThreePivotEnvelope.actual_last_three_envelope
#print axioms Rho5.LastThreePivotEnvelope.actual_last_three_envelope

/-! ## 真实 `delta` 的三种符号 -/

#print Rho5.LastThreePivotEnvelope.delta_sign_trichotomy
#print axioms Rho5.LastThreePivotEnvelope.delta_sign_trichotomy

#print Rho5.LastThreePivotEnvelope.envelope_delta_zero
#print axioms Rho5.LastThreePivotEnvelope.envelope_delta_zero

#print Rho5.LastThreePivotEnvelope.envelope_delta_neg
#print axioms Rho5.LastThreePivotEnvelope.envelope_delta_neg

#print Rho5.LastThreePivotEnvelope.envelope_delta_pos
#print axioms Rho5.LastThreePivotEnvelope.envelope_delta_pos

/-! ## 阶段 B —— 全局 `rho5Trace ≤ 81/16` -/

#print Rho5.LastThreePivotEnvelope.nested_secondPivot_eq_secondMagnitude
#print axioms Rho5.LastThreePivotEnvelope.nested_secondPivot_eq_secondMagnitude

#print Rho5.LastThreePivotEnvelope.nested_thirdPivot_eq_thirdMagnitude
#print axioms Rho5.LastThreePivotEnvelope.nested_thirdPivot_eq_thirdMagnitude

#print Rho5.LastThreePivotEnvelope.nested_normalized_iff_d83
#print axioms Rho5.LastThreePivotEnvelope.nested_normalized_iff_d83

#print Rho5.LastThreePivotEnvelope.p_le_two
#print axioms Rho5.LastThreePivotEnvelope.p_le_two

#print Rho5.LastThreePivotEnvelope.k_le_nine_quarters
#print axioms Rho5.LastThreePivotEnvelope.k_le_nine_quarters

#print Rho5.LastThreePivotEnvelope.r_div_p_le_nine_quarters
#print axioms Rho5.LastThreePivotEnvelope.r_div_p_le_nine_quarters

#print Rho5.LastThreePivotEnvelope.r_le_nine_halves
#print axioms Rho5.LastThreePivotEnvelope.r_le_nine_halves

#print Rho5.LastThreePivotEnvelope.delta_abs_le_eighty_one_sixteenth
#print axioms Rho5.LastThreePivotEnvelope.delta_abs_le_eighty_one_sixteenth

#print Rho5.LastThreePivotEnvelope.five_value_peak_le_eighty_one_sixteenth
#print axioms Rho5.LastThreePivotEnvelope.five_value_peak_le_eighty_one_sixteenth

#print Rho5.LastThreePivotEnvelope.growthRatio_le_eighty_one_sixteenth
#print axioms Rho5.LastThreePivotEnvelope.growthRatio_le_eighty_one_sixteenth

#print Rho5.LastThreePivotEnvelope.polyCP_inequalities_eighty_one_sixteenth
#print axioms Rho5.LastThreePivotEnvelope.polyCP_inequalities_eighty_one_sixteenth

#print Rho5.LastThreePivotEnvelope.rho5Trace_le_eighty_one_sixteenth
#print axioms Rho5.LastThreePivotEnvelope.rho5Trace_le_eighty_one_sixteenth

#print Rho5.LastThreePivotEnvelope.eighty_one_sixteenth_lt_ten_point_one
#print axioms Rho5.LastThreePivotEnvelope.eighty_one_sixteenth_lt_ten_point_one

#print Rho5.LastThreePivotEnvelope.rho5Trace_le_eighty_one_sixteenth_and_improves
#print axioms Rho5.LastThreePivotEnvelope.rho5Trace_le_eighty_one_sixteenth_and_improves
