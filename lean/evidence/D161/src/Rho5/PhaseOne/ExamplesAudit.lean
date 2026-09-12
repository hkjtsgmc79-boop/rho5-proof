import Rho5.PhaseOne.Examples

/-! D161 独立审计薄入口（**不**被产品默认 import）：打印本卡示例与所引用 C02 定理的
完整类型与 `#print axioms`，确认两个全域安全前提仍然显式可见。 -/
set_option pp.universes true

#check @Rho5.PhaseOne.Examples.alpha_unique_root_in_four_five
#print axioms Rho5.PhaseOne.Examples.alpha_unique_root_in_four_five

#check @Rho5.PhaseOne.Examples.alpha_readings
#print axioms Rho5.PhaseOne.Examples.alpha_readings

#check @Rho5.PhaseOne.Examples.rho5Trace_is_sSup
#print axioms Rho5.PhaseOne.Examples.rho5Trace_is_sSup

#check @Rho5.PhaseOne.Examples.actual_alpha_attained
#print axioms Rho5.PhaseOne.Examples.actual_alpha_attained

#check @Rho5.PhaseOne.Examples.alpha_le_rho5Trace_le_eighty_one_sixteenth
#print axioms Rho5.PhaseOne.Examples.alpha_le_rho5Trace_le_eighty_one_sixteenth

#check @Rho5.PhaseOne.Examples.four_lt_rho5Trace
#print axioms Rho5.PhaseOne.Examples.four_lt_rho5Trace

#check @Rho5.PhaseOne.Examples.exists_global_maximizer
#print axioms Rho5.PhaseOne.Examples.exists_global_maximizer

#check @Rho5.PhaseOne.Examples.rho5Trace_eq_alpha
#print axioms Rho5.PhaseOne.Examples.rho5Trace_eq_alpha

#check @Rho5.PhaseOne.Examples.legal_growth_le_alpha
#print axioms Rho5.PhaseOne.Examples.legal_growth_le_alpha

#check @Rho5.PhaseOne.Examples.fifth_readout_le_alpha
#print axioms Rho5.PhaseOne.Examples.fifth_readout_le_alpha

#check @Rho5.PhaseOne.Examples.high_path_fifth
#print axioms Rho5.PhaseOne.Examples.high_path_fifth

#check @Rho5.PhaseOne.Examples.det_endpoint
#print axioms Rho5.PhaseOne.Examples.det_endpoint

#check @Rho5.PhaseOne.Examples.xGlobalSafety_shape
#print axioms Rho5.PhaseOne.Examples.xGlobalSafety_shape

#check @Rho5.PhaseOne.Examples.rootEndpointSafety_shape
#print axioms Rho5.PhaseOne.Examples.rootEndpointSafety_shape

/-! 被消费的 C02 条件入口（完整类型，确认 hX/hB 仍显式）： -/
#check @Rho5.Integration.StagedAssembly.rho5Trace_eq_alpha_of_safety
#check @Rho5.Integration.StagedAssembly.legal_growth_le_alpha_of_safety
#check @Rho5.Integration.StagedAssembly.baseline
