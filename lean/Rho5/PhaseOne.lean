import Rho5.Integration.StagedAssembly.Conditional
import Rho5.ExternalV43Existence.PhysicalTrip

/-!
# Phase one: accepted reductions and explicit conditional endpoints

This entry exposes the accepted C02 rebound mainline and D84 actual local ODE
trajectories. All exported names retain their original theorem types and proofs.
The sharp equality still requires the full original XGlobalSafety and
RootEndpointSafety. Local trajectories keep their starting-region and budget
hypotheses. No global safety certificate is supplied here.

Default imports exclude PhaseOne.Examples, PhaseOne.Audit and phase-two trees.
-/
namespace Rho5.PhaseOne

export Rho5.Integration.StagedAssembly
  (baseline
   exists_global_max_X_or_root_endpoint
   exists_X_or_root_endpoint
   XGlobalSafety
   rho5Trace_eq_alpha_of_safety
   legal_growth_le_alpha_of_safety
   fifth_readout_le_alpha_of_safety
   legal_growth_le_alpha_via_fifth_of_safety
   high_path_fifth_of_safety
   det_endpoint_of_safety)

export Rho5.Shared.BRootCapacityEndpoint
  (IsRootCapacityEndpoint
   RootEndpointSafety)

export Rho5.Algebraic.AlphaRoot
  (exists_root_in_exact_interval
   alpha_in_exact_interval
   alpha_is_root
   exists_unique_root
   root_unique
   alpha_gt_four
   alpha_lt_five)

export Rho5.ExternalAttainment
  (actualAlpha_attainment
   exists_actualAlpha_attainment
   actualAlpha_le_rho5Trace)

export Rho5.ExternalFourthPivot
  (early_pivot_bounds_including_zero
   growth_above_four_is_fifth
   growth_le_of_fifth_readout_le)

export Rho5.ExternalV43Existence
  (exists_actual_trajectory_on_time_neighborhood
   exists_actual_trajectory
   exists_physical_trajectory
   exists_resource_endpoint
   exists_exhaustion_at_own_resource
   exists_guard_boundary_trajectory
   exists_zero_time_actual_derivative
   height_le_of_actual_trip)

end Rho5.PhaseOne
