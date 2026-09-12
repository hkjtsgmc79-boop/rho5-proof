/-
D84 — layer audit for the successfully compiled REGULARITY layer (Geometry + Regularity).

This is a lane-added audit file (not part of the external package): the package's own
`Audit.lean` needs the aggregate, which in turn needs the not-yet-cached ODE modules.
-/
import Rho5.ExternalV43Existence.Regularity

#print axioms Rho5.ExternalV43Existence.radius_nonneg_of_mem_cube
#print axioms Rho5.ExternalV43Existence.closedBall_subset_cube
#print axioms Rho5.ExternalV43Existence.finite_horizon_margins
#print axioms Rho5.ExternalV43Existence.expr_contDiff_two
#print axioms Rho5.ExternalV43Existence.actual_chart_contDiff_two
#print axioms Rho5.ExternalV43Existence.actual_chartD_eq_fderiv
#print axioms Rho5.ExternalV43Existence.actual_jacobian_contDiff_one
#print axioms Rho5.ExternalV43Existence.inverseFormula_contDiffAt
#print axioms Rho5.ExternalV43Existence.inverseFormula_eq_inward
#print axioms Rho5.ExternalV43Existence.inverseFormula_eq_certifiedField
#print axioms Rho5.ExternalV43Existence.certifiedField_lipschitz_on_closedBall

#check @Rho5.ExternalV43Existence.radius_nonneg_of_mem_cube
#check @Rho5.ExternalV43Existence.closedBall_subset_cube
#check @Rho5.ExternalV43Existence.finite_horizon_margins
#check @Rho5.ExternalV43Existence.actual_chart_contDiff_two
#check @Rho5.ExternalV43Existence.actual_chartD_eq_fderiv
#check @Rho5.ExternalV43Existence.certifiedField_lipschitz_on_closedBall
#check @Rho5.ExternalV43Existence.expr_contDiff_two
#check @Rho5.ExternalV43Existence.actual_jacobian_contDiff_one
#check @Rho5.ExternalV43Existence.inverseFormula_eq_inward
#check @Rho5.ExternalV43Existence.inverseFormula_eq_certifiedField
#check @Rho5.ExternalV43Existence.inverseFormula_contDiffAt
