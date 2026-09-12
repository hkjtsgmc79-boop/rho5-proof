import Rho5.Shared.TailSaturationBounds.InputBounds

/-!
# D125 — high-value growth domination, with the last-entry premises paid internally

On the same real TS input, if the actual fifth readout `height M = |delta M|` is above `4`, then
all four dominance premises of D122's `same_growth_if_last_dominates` are paid **inside** this
theorem from `input_early_bounds`:

* `1 ≤ height M`;
* `p M ≤ height M`, `k M ≤ height M`, `|r M| ≤ height M` (in fact the strict readings
  `p M < height M`, `k M < height M`, `|r M| < height M`).

The conclusion assembles only already-proved results: the original real trace's growth equals the
height, the **actual D-or-X contracted matrix** `representative M` with the same last entry
(`height (representative M) = height M`), the same `p`, `k`, `delta`, the non-increasing fourth
pivot `|r (representative M)| ≤ |r M|`, its real legal trace and its growth equal to the same
height.  The user no longer has to supply the last-entry dominance.  No contraction mathematics
is re-proved and no new alpha bound is claimed.
-/

noncomputable section
namespace Rho5.Shared.TailSaturationBounds

open Rho5
open Rho5.Certificate.B24Extraction (p k r)
open Rho5.ExternalTailSaturation (LeadingInput height DFace XFace representative representative_spec
  same_growth_if_last_dominates chosenLambda chosenMu delta)

/-- **High-value tail growth**: under `4 < height M` the original and the contracted real traces
both have growth exactly `height M`, with the four dominance premises paid here from
`input_early_bounds` and every strict reading displayed. -/
theorem input_growth_eq_height_of_high {M : Matrix5} (h : LeadingInput M)
    (hhigh : 4 < height M) :
    p M < height M ∧ k M < height M ∧ |r M| < height M ∧ (1 : ℝ) ≤ height M ∧
    Rho5.GrowthModel.growthRatio M [1, p M, k M, |r M|, height M] = height M ∧
    (DFace (representative M) ∨ XFace (representative M)) ∧
    height (representative M) = height M ∧
    p (representative M) = p M ∧ k (representative M) = k M ∧
    delta (representative M) = delta M ∧
    |r (representative M)| ≤ |r M| ∧
    Rho5.CompletePivotPath.LegalTrace (representative M)
      [1, p M, k M, |chosenLambda M * chosenMu M * r M|, height M] ∧
    Rho5.GrowthModel.growthRatio (representative M)
      [1, p M, k M, |chosenLambda M * chosenMu M * r M|, height M] = height M := by
  obtain ⟨hp, hk, hr⟩ := input_early_bounds h
  have h1 : (1 : ℝ) ≤ height M := by linarith
  have hpm : p M ≤ height M := by linarith
  have hkm : k M ≤ height M := by linarith
  have hrm : |r M| ≤ height M := by linarith
  obtain ⟨-, htraceR, hgrowthM, hgrowthR⟩ :=
    same_growth_if_last_dominates h h1 hpm hkm hrm
  obtain ⟨-, hpR, hkR, hdeltaR, hheightR, hrR, -, hface, -⟩ := representative_spec h
  exact ⟨by linarith, by linarith, by linarith, h1, hgrowthM, hface, hheightR, hpR, hkR, hdeltaR,
    hrR, htraceR, hgrowthR⟩

end Rho5.Shared.TailSaturationBounds
