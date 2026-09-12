import Rho5.Shared.LastThreePivotEnvelope
import Rho5.ExternalAttainment.ActualAlpha
import Rho5.Algebraic.AlphaRoot.Root

/-!
# D92 phase A — the global range of `rho5Trace` and `alpha`

Consumes three already-accepted results and nothing else:

* D09 `Rho5.Algebraic.AlphaRoot.alpha_gt_four` — `4 < alpha` (algebraic isolation of alpha);
* D82 `Rho5.ExternalAttainment.actualAlpha_le_rho5Trace` — `alpha ≤ rho5Trace`
  (the actual candidate matrix at the accepted G04 critical point attains `alpha`);
* D87 `Rho5.LastThreePivotEnvelope.rho5Trace_le_eighty_one_sixteenth` — `rho5Trace ≤ 81/16`.

Conclusions: `4 < rho5Trace`, `alpha ≤ rho5Trace ≤ 81/16` and `alpha ≤ 81/16`.
The original semantics of `rho5Trace` (`sSup GrowthValues`) is **not** changed: the module
only cites `Rho5.GrowthSupremum.rho5Trace` and its paid `rho5Trace_eq`.
-/

noncomputable section
namespace Rho5.Shared.GlobalAttainedWitness

open Rho5

/-- The original definition of the global constant is untouched: it is still the supremum
of the original growth-value set. -/
theorem rho5Trace_semantics :
    Rho5.GrowthSupremum.rho5Trace = sSup Rho5.GrowthModel.GrowthValues :=
  Rho5.GrowthSupremum.rho5Trace_eq

/-- D09: the algebraic `alpha` is strictly bigger than `4`. -/
theorem alpha_gt_four : (4 : ℝ) < Rho5.Algebraic.AlphaRoot.alpha :=
  Rho5.Algebraic.AlphaRoot.alpha_gt_four

/-- D82: the actual candidate at the accepted G04 critical point attains `alpha`, so
`alpha ≤ rho5Trace`. -/
theorem alpha_le_rho5Trace :
    Rho5.Algebraic.AlphaRoot.alpha ≤ Rho5.GrowthSupremum.rho5Trace :=
  Rho5.ExternalAttainment.actualAlpha_le_rho5Trace

/-- D87: the accepted unconditional global upper bound. -/
theorem rho5Trace_le_eighty_one_sixteenth :
    Rho5.GrowthSupremum.rho5Trace ≤ (81 : ℝ) / 16 :=
  Rho5.LastThreePivotEnvelope.rho5Trace_le_eighty_one_sixteenth

/-- **Phase A headline**: the global constant is strictly above the closed-box threshold. -/
theorem four_lt_rho5Trace : (4 : ℝ) < Rho5.GrowthSupremum.rho5Trace :=
  lt_of_lt_of_le alpha_gt_four alpha_le_rho5Trace

/-- `alpha` inherits the D87 upper bound. -/
theorem alpha_le_eighty_one_sixteenth :
    Rho5.Algebraic.AlphaRoot.alpha ≤ (81 : ℝ) / 16 :=
  le_trans alpha_le_rho5Trace rho5Trace_le_eighty_one_sixteenth

/-- The two-sided range of the original global constant. -/
theorem rho5Trace_mem_range :
    (4 : ℝ) < Rho5.GrowthSupremum.rho5Trace ∧
      Rho5.GrowthSupremum.rho5Trace ≤ (81 : ℝ) / 16 :=
  ⟨four_lt_rho5Trace, rho5Trace_le_eighty_one_sixteenth⟩

/-- The same range for `alpha`. -/
theorem alpha_mem_range :
    (4 : ℝ) < Rho5.Algebraic.AlphaRoot.alpha ∧
      Rho5.Algebraic.AlphaRoot.alpha ≤ (81 : ℝ) / 16 :=
  ⟨alpha_gt_four, alpha_le_eighty_one_sixteenth⟩

end Rho5.Shared.GlobalAttainedWitness
