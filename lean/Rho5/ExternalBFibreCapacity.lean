import Rho5.ExternalBFibreCapacity.Attainment
import Rho5.ExternalBFibreCapacity.Nonempty

/-!
Exact same-source normalized negative-D fibre capacity.

Primary declarations:
* `complete_fibre_argmax`: explicit attained maximum over a whole 17D frame fibre;
* `three_path_endpoints`, `betaPath_spec`, `pePath_spec`, `tailPath_spec`,
  `tailPath_height_monotone`: the three complete, real B24 paths;
* `complete_fibre_nonempty_iff`: literal interval/receiver/fixed-cell checks;
* `actual_matrix_attainment`: actual reconstruction and the frozen LegalTrace;
* `actual_growth_eq_capacity`: exact growth only under explicit pivot dominance.

This source makes no statement about AlphaRoot, a global B17 box, arbitrary-matrix
normalization, or the already-completed numerical proof. Build status is supplied
separately; a Python check is not a substitute for Lean elaboration.
-/
