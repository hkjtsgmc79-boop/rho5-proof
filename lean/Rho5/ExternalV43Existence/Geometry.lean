import Rho5.LocalAnalysis.Model
-- D84 lane adaptation (2026-09-12): `Mathlib.Analysis.Normed.Module.FiniteDimension` is not cached in
-- this environment and is UNUSED by this file's proofs (they use only `norm_le_pi_norm`,
-- `abs_sub_le`, `closedBall`/`cube` and `linarith`).  The import is therefore dropped in this lane
-- copy so that the Geometry/Regularity layer can be compiled and audited now; the A1 layer still
-- requires that module together with `Mathlib.Analysis.ODE.PicardLindelof` (see results/REPORT.md).
import Mathlib.Tactic.Linarith

/-!
# Geometry for the actual V43 finite-time trajectory

Only elementary sup-norm geometry is new here.  In particular, `cube` is the
unchanged coordinatewise closed cube from the supplied project.
-/

namespace Rho5.ExternalV43Existence
noncomputable section
open Rho5.LocalAnalysis Set Metric

/-- A nonempty coordinate cube cannot have negative radius. -/
theorem radius_nonneg_of_mem_cube {c z : X} {d : ℝ}
    (hz : z ∈ cube c d) : 0 ≤ d :=
  (abs_nonneg (z 0 - c 0)).trans (hz 0)

/-- A sup-norm ball about an actual source is contained in the original cube.
No assertion about physical feasibility is made for arbitrary points of the ball. -/
theorem closedBall_subset_cube {c z0 : X} {d a ρ : ℝ}
    (hstart : z0 ∈ cube c d) (hsize : d + a ≤ ρ) :
    closedBall z0 a ⊆ cube c ρ := by
  intro z hz i
  have hn : ‖z - z0‖ ≤ a := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hi : |z i - z0 i| ≤ ‖z - z0‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (z - z0) i
  have htri := abs_sub_le (z i) (z0 i) (c i)
  have hci := hstart i
  linarith

/-- Explicit spare spatial and temporal radii.  This lemma is independent of
ODE existence and includes T=0.  The speed is the frozen V43 value 9/4. -/
theorem finite_horizon_margins {d T ρ : ℝ}
    (hT : 0 ≤ T) (hbudget : d + (9 / 4 : ℝ) * T < ρ) :
    let m := ρ - d - (9 / 4 : ℝ) * T
    let a := (9 / 4 : ℝ) * T + m / 2
    let ε := m / 9
    0 < m ∧ 0 < a ∧ 0 < ε ∧ d + a < ρ ∧
      (9 / 4 : ℝ) * (T + ε) ≤ a := by
  dsimp
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end
end Rho5.ExternalV43Existence
