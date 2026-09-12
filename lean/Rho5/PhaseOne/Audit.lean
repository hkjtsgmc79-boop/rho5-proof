import Rho5.PhaseOne

set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false
set_option format.width 120

#check @Rho5.PhaseOne.baseline
#print axioms Rho5.PhaseOne.baseline

#check @Rho5.PhaseOne.exists_global_max_X_or_root_endpoint
#print axioms Rho5.PhaseOne.exists_global_max_X_or_root_endpoint

#check @Rho5.PhaseOne.exists_X_or_root_endpoint
#print axioms Rho5.PhaseOne.exists_X_or_root_endpoint

#check @Rho5.PhaseOne.XGlobalSafety
#print axioms Rho5.PhaseOne.XGlobalSafety

#check @Rho5.PhaseOne.rho5Trace_eq_alpha_of_safety
#print axioms Rho5.PhaseOne.rho5Trace_eq_alpha_of_safety

#check @Rho5.PhaseOne.legal_growth_le_alpha_of_safety
#print axioms Rho5.PhaseOne.legal_growth_le_alpha_of_safety

#check @Rho5.PhaseOne.fifth_readout_le_alpha_of_safety
#print axioms Rho5.PhaseOne.fifth_readout_le_alpha_of_safety

#check @Rho5.PhaseOne.legal_growth_le_alpha_via_fifth_of_safety
#print axioms Rho5.PhaseOne.legal_growth_le_alpha_via_fifth_of_safety

#check @Rho5.PhaseOne.high_path_fifth_of_safety
#print axioms Rho5.PhaseOne.high_path_fifth_of_safety

#check @Rho5.PhaseOne.det_endpoint_of_safety
#print axioms Rho5.PhaseOne.det_endpoint_of_safety

#check @Rho5.PhaseOne.IsRootCapacityEndpoint
#print axioms Rho5.PhaseOne.IsRootCapacityEndpoint

#check @Rho5.PhaseOne.RootEndpointSafety
#print axioms Rho5.PhaseOne.RootEndpointSafety

#check @Rho5.PhaseOne.exists_root_in_exact_interval
#print axioms Rho5.PhaseOne.exists_root_in_exact_interval

#check @Rho5.PhaseOne.alpha_in_exact_interval
#print axioms Rho5.PhaseOne.alpha_in_exact_interval

#check @Rho5.PhaseOne.alpha_is_root
#print axioms Rho5.PhaseOne.alpha_is_root

#check @Rho5.PhaseOne.exists_unique_root
#print axioms Rho5.PhaseOne.exists_unique_root

#check @Rho5.PhaseOne.root_unique
#print axioms Rho5.PhaseOne.root_unique

#check @Rho5.PhaseOne.alpha_gt_four
#print axioms Rho5.PhaseOne.alpha_gt_four

#check @Rho5.PhaseOne.alpha_lt_five
#print axioms Rho5.PhaseOne.alpha_lt_five

#check @Rho5.PhaseOne.actualAlpha_attainment
#print axioms Rho5.PhaseOne.actualAlpha_attainment

#check @Rho5.PhaseOne.exists_actualAlpha_attainment
#print axioms Rho5.PhaseOne.exists_actualAlpha_attainment

#check @Rho5.PhaseOne.actualAlpha_le_rho5Trace
#print axioms Rho5.PhaseOne.actualAlpha_le_rho5Trace

#check @Rho5.PhaseOne.early_pivot_bounds_including_zero
#print axioms Rho5.PhaseOne.early_pivot_bounds_including_zero

#check @Rho5.PhaseOne.growth_above_four_is_fifth
#print axioms Rho5.PhaseOne.growth_above_four_is_fifth

#check @Rho5.PhaseOne.growth_le_of_fifth_readout_le
#print axioms Rho5.PhaseOne.growth_le_of_fifth_readout_le

#check @Rho5.PhaseOne.exists_actual_trajectory_on_time_neighborhood
#print axioms Rho5.PhaseOne.exists_actual_trajectory_on_time_neighborhood

#check @Rho5.PhaseOne.exists_actual_trajectory
#print axioms Rho5.PhaseOne.exists_actual_trajectory

#check @Rho5.PhaseOne.exists_physical_trajectory
#print axioms Rho5.PhaseOne.exists_physical_trajectory

#check @Rho5.PhaseOne.exists_resource_endpoint
#print axioms Rho5.PhaseOne.exists_resource_endpoint

#check @Rho5.PhaseOne.exists_exhaustion_at_own_resource
#print axioms Rho5.PhaseOne.exists_exhaustion_at_own_resource

#check @Rho5.PhaseOne.exists_guard_boundary_trajectory
#print axioms Rho5.PhaseOne.exists_guard_boundary_trajectory

#check @Rho5.PhaseOne.exists_zero_time_actual_derivative
#print axioms Rho5.PhaseOne.exists_zero_time_actual_derivative

#check @Rho5.PhaseOne.height_le_of_actual_trip
#print axioms Rho5.PhaseOne.height_le_of_actual_trip

#print Rho5.Integration.StagedAssembly.GlobalMaximizerReductionFacts
#print Rho5.Integration.StagedAssembly.ActualXBranch
#print Rho5.Integration.StagedAssembly.ActualBRootEndpointBranch
#print Rho5.Integration.StagedAssembly.XGlobalSafety
#print Rho5.Shared.BRootCapacityEndpoint.IsRootCapacityEndpoint
#print Rho5.Shared.BRootCapacityEndpoint.RootEndpointSafety

run_cmd do
  let env ← Lean.getEnv
  for m in env.header.moduleNames do
    if m.toString.startsWith "Rho5." then
      Lean.logInfo m!"P01_LOADED_MODULE {m}"
