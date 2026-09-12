import Rho5.ExternalAttainment.Attainment
import Rho5.Algebraic.CriticalExistence.ActualAlpha
import Rho5.Shared.GrowthSupremum

/-!
# D82 phase B — the actual candidate at the accepted G04 critical point

Phase A proved, from the original `CandidateBox` and `P1 = P2 = P3 = 0`, that the actual
candidate matrix `candidateMatrix x y z g` has entry maximum `1`, carries the original
`LegalTrace` values `[1, 1+z, p3, g/2, g]` and has growth ratio `g`.

This module feeds the **accepted G04 closed-box critical point** into that theorem:

* `criticalPoint` is the unique point of the original closed box satisfying the critical
  system (`Rho5.Algebraic.CriticalExistence.criticalPoint_original`);
* `criticalPoint_g_eq_alpha` identifies its last coordinate with `AlphaRoot.alpha`, via the
  accepted D34 bridge `Rho5.Algebraic.ScalarCandidateAlpha` (so the `g` of the candidate
  configuration **is** the actual `alpha`);
* hence `AlphaRoot.alpha` is an original growth value and a normalized growth value, and
  `AlphaRoot.alpha ≤ rho5Trace`.

Only the G04 box and `P1 = P2 = P3 = 0` are used; the Jacobian equation `J` of G04 exists
but is not needed (it is not part of this module's hypotheses).  No claim is made about
`rho5Trace ≤ alpha`, i.e. `rho5Trace = alpha` is **not** asserted here.
-/

noncomputable section
namespace Rho5.ExternalAttainment

open Rho5

/-- First coordinate of the accepted G04 critical point (the original variable `x`). -/
def criticalX : ℝ := Rho5.Algebraic.CriticalExistence.criticalPoint 0

/-- Second coordinate of the accepted G04 critical point (the original variable `y`). -/
def criticalY : ℝ := Rho5.Algebraic.CriticalExistence.criticalPoint 1

/-- Third coordinate of the accepted G04 critical point (the original variable `z`). -/
def criticalZ : ℝ := Rho5.Algebraic.CriticalExistence.criticalPoint 2

/-- Fourth coordinate of the accepted G04 critical point (the original variable `g`). -/
def criticalG : ℝ := Rho5.Algebraic.CriticalExistence.criticalPoint 3

/-- **The actual matrix**: the candidate matrix of `Formulas.lean` evaluated at the accepted
critical point.  It is a genuine `Rho5.Matrix5`, not an abstract witness. -/
def actualAlphaMatrix : Rho5.Matrix5 :=
  candidateMatrix criticalX criticalY criticalZ Rho5.Algebraic.AlphaRoot.alpha

/-- **The original `LegalTrace` values** of that matrix: `[1, 1+z, p3, g/2, g]`. -/
def actualAlphaValues : List ℝ :=
  candidateValues criticalX criticalY criticalZ Rho5.Algebraic.AlphaRoot.alpha

/-- The last coordinate of the accepted critical point **is** `AlphaRoot.alpha`
(accepted D34 bridge, consumed as-is). -/
theorem criticalG_eq_alpha : criticalG = Rho5.Algebraic.AlphaRoot.alpha :=
  Rho5.Algebraic.CriticalExistence.criticalPoint_g_eq_alpha

/-- The accepted critical point lies in the original closed `CandidateBox`. -/
theorem actualAlpha_box :
    Rho5.Algebraic.CandidateBox criticalX criticalY criticalZ criticalG := by
  obtain ⟨hb, -, -, -, -⟩ := Rho5.Algebraic.CriticalExistence.criticalPoint_original
  simpa only [criticalX, criticalY, criticalZ, criticalG] using hb

/-- First original root equation at the accepted critical point. -/
theorem actualAlpha_P1 : Rho5.Algebraic.P1 criticalX criticalY criticalZ criticalG = 0 := by
  obtain ⟨-, h1, -, -, -⟩ := Rho5.Algebraic.CriticalExistence.criticalPoint_original
  simpa only [criticalX, criticalY, criticalZ, criticalG] using h1

/-- Second original root equation at the accepted critical point. -/
theorem actualAlpha_P2 : Rho5.Algebraic.P2 criticalX criticalY criticalZ criticalG = 0 := by
  obtain ⟨-, -, h2, -, -⟩ := Rho5.Algebraic.CriticalExistence.criticalPoint_original
  simpa only [criticalX, criticalY, criticalZ, criticalG] using h2

/-- Third original root equation at the accepted critical point. -/
theorem actualAlpha_P3 : Rho5.Algebraic.P3 criticalX criticalY criticalZ criticalG = 0 := by
  obtain ⟨-, -, -, h3, -⟩ := Rho5.Algebraic.CriticalExistence.criticalPoint_original
  simpa only [criticalX, criticalY, criticalZ, criticalG] using h3

/-- **Phase B headline**: the actual matrix at the accepted critical point has entry maximum
`1`, carries the original `LegalTrace` values, has growth ratio exactly `AlphaRoot.alpha`,
and `AlphaRoot.alpha` is both an original and a normalized growth value. -/
theorem actualAlpha_attainment :
    Rho5.matrixEntryMax actualAlphaMatrix = 1 ∧
      Rho5.CompletePivotPath.LegalTrace actualAlphaMatrix actualAlphaValues ∧
      Rho5.GrowthModel.growthRatio actualAlphaMatrix actualAlphaValues =
        Rho5.Algebraic.AlphaRoot.alpha ∧
      Rho5.Algebraic.AlphaRoot.alpha ∈ Rho5.GrowthModel.GrowthValues ∧
      Rho5.Algebraic.AlphaRoot.alpha ∈ Rho5.GrowthModel.NormalizedGrowthValues := by
  obtain ⟨hm, ht, hr, hg, hn⟩ :=
    candidate_attainment actualAlpha_box actualAlpha_P1 actualAlpha_P2 actualAlpha_P3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [actualAlphaMatrix, criticalG_eq_alpha] using hm
  · simpa only [actualAlphaMatrix, actualAlphaValues, criticalG_eq_alpha] using ht
  · simpa only [actualAlphaMatrix, actualAlphaValues, criticalG_eq_alpha] using hr
  · simpa only [criticalG_eq_alpha] using hg
  · simpa only [criticalG_eq_alpha] using hn

/-- `AlphaRoot.alpha` is an original growth value (attained by an actual matrix). -/
theorem actualAlpha_mem_GrowthValues :
    Rho5.Algebraic.AlphaRoot.alpha ∈ Rho5.GrowthModel.GrowthValues :=
  actualAlpha_attainment.2.2.2.1

/-- `AlphaRoot.alpha` is a normalized growth value. -/
theorem actualAlpha_mem_NormalizedGrowthValues :
    Rho5.Algebraic.AlphaRoot.alpha ∈ Rho5.GrowthModel.NormalizedGrowthValues :=
  actualAlpha_attainment.2.2.2.2

/-- **Phase B endpoint**: `AlphaRoot.alpha ≤ rho5Trace`, through the paid
`Rho5.GrowthSupremum.le_rho5Trace`.  The converse is **not** claimed. -/
theorem actualAlpha_le_rho5Trace :
    Rho5.Algebraic.AlphaRoot.alpha ≤ Rho5.GrowthSupremum.rho5Trace :=
  Rho5.GrowthSupremum.le_rho5Trace actualAlpha_mem_GrowthValues

/-- Existential packaging of the same statement, for consumers that prefer a witness. -/
theorem exists_actualAlpha_attainment :
    ∃ x y z : ℝ,
      Rho5.matrixEntryMax (candidateMatrix x y z Rho5.Algebraic.AlphaRoot.alpha) = 1 ∧
        Rho5.CompletePivotPath.LegalTrace
          (candidateMatrix x y z Rho5.Algebraic.AlphaRoot.alpha)
          (candidateValues x y z Rho5.Algebraic.AlphaRoot.alpha) ∧
        Rho5.GrowthModel.growthRatio
          (candidateMatrix x y z Rho5.Algebraic.AlphaRoot.alpha)
          (candidateValues x y z Rho5.Algebraic.AlphaRoot.alpha) =
            Rho5.Algebraic.AlphaRoot.alpha ∧
        Rho5.Algebraic.AlphaRoot.alpha ∈ Rho5.GrowthModel.GrowthValues ∧
        Rho5.Algebraic.AlphaRoot.alpha ∈ Rho5.GrowthModel.NormalizedGrowthValues ∧
        Rho5.Algebraic.AlphaRoot.alpha ≤ Rho5.GrowthSupremum.rho5Trace := by
  refine ⟨criticalX, criticalY, criticalZ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [actualAlphaMatrix] using actualAlpha_attainment.1
  · simpa only [actualAlphaMatrix, actualAlphaValues] using actualAlpha_attainment.2.1
  · simpa only [actualAlphaMatrix, actualAlphaValues] using actualAlpha_attainment.2.2.1
  · exact actualAlpha_mem_GrowthValues
  · exact actualAlpha_mem_NormalizedGrowthValues
  · exact actualAlpha_le_rho5Trace

end Rho5.ExternalAttainment
