/-
D18 — the growth value set is nonempty
======================================

**Item 1.** `Rho5.GrowthModel.GrowthValues` is nonempty.  The witness is *concrete*:

* the all-ones `5 × 5` matrix `oneMatrix` is nonzero (`oneMatrix_ne_zero`) and has
  frozen entry maximum `1` (`matrixEntryMax_oneMatrix`, D17's `matrixEntryMax_const_one`);
* D14's `exists_legalTrace` (reused, not reproved) supplies a legal trace of it — here
  through D14's noncomputable `chosenTrace`, whose legality is `chosenTrace_spec`;
* the growth ratio of that trace is therefore a member of `GrowthValues`.

No path existence is assumed: D14 is the module that pays it.  The normalized set is
inhabited as well, both through D17's set equality and by a direct witness.
-/
import Rho5.Shared.GrowthModel
import Rho5.Shared.TraceExistence

namespace Rho5.GrowthSupremum

open Rho5

/-! ## The concrete witness matrix -/

/-- The all-ones `5 × 5` real matrix: the explicit nonzero witness used for
nonemptiness.  (D17 already proves its frozen entry maximum is `1`.) -/
def oneMatrix : Matrix5 := fun _ _ => (1 : ℝ)

/-- Entry value of the witness. -/
theorem oneMatrix_apply (i j : Fin 5) : oneMatrix i j = (1 : ℝ) := rfl

/-- The witness is nonzero (its `(0, 0)` entry is `1`). -/
theorem oneMatrix_ne_zero : oneMatrix ≠ 0 := by
  intro h
  have h00 : oneMatrix 0 0 = (0 : Matrix5) 0 0 := congrFun (congrFun h 0) 0
  simp [oneMatrix] at h00

/-- The witness has frozen entry maximum `1` (D17's `matrixEntryMax_const_one`). -/
theorem matrixEntryMax_oneMatrix : matrixEntryMax oneMatrix = 1 :=
  Rho5.GrowthModel.matrixEntryMax_const_one

/-! ## Nonemptiness -/

/-- **Item 1 (explicit member).** The growth ratio of the D14-chosen trace of the
all-ones matrix is an actual member of `GrowthValues`. -/
theorem oneMatrix_growthRatio_mem :
    Rho5.GrowthModel.growthRatio oneMatrix (Rho5.TraceExistence.chosenTrace oneMatrix) ∈
      Rho5.GrowthModel.GrowthValues :=
  ⟨oneMatrix, _, oneMatrix_ne_zero, Rho5.TraceExistence.chosenTrace_spec oneMatrix, rfl⟩

/-- **Item 1 (nonemptiness).** `GrowthValues` is nonempty. -/
theorem growthValues_nonempty : Rho5.GrowthModel.GrowthValues.Nonempty :=
  ⟨_, oneMatrix_growthRatio_mem⟩

/-- **Item 1 (normalized witness).** The peak of the D14-chosen trace of the
all-ones matrix is an actual member of `NormalizedGrowthValues`: the witness matrix
already has entry maximum `1`. -/
theorem oneMatrix_tracePeak_mem :
    Rho5.GrowthModel.tracePeak (Rho5.TraceExistence.chosenTrace oneMatrix) ∈
      Rho5.GrowthModel.NormalizedGrowthValues :=
  ⟨oneMatrix, _, matrixEntryMax_oneMatrix,
   Rho5.TraceExistence.chosenTrace_spec oneMatrix, rfl⟩

/-- **Item 1 (normalized nonemptiness).** `NormalizedGrowthValues` is nonempty,
via D17's frozen set equality. -/
theorem normalizedGrowthValues_nonempty :
    Rho5.GrowthModel.NormalizedGrowthValues.Nonempty := by
  rw [← Rho5.GrowthModel.growthValues_eq_normalized]
  exact growthValues_nonempty

end Rho5.GrowthSupremum
