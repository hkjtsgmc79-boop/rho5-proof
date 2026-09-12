import Rho5.Certificate.B24Extraction.Bands
import Rho5.Certificate.B24MinorBridge.Witness
import Rho5.ExternalBFibreCapacity.Model
import Rho5.ExternalTailSaturation.Basic
import Rho5.ExternalTailSaturation.Signs

/-!
# D130 — the real gap between a proper-B representative and `Rho5.ExternalBFibreCapacity.NormalizedB`

`NormalizedB z` is `Qualified z ∧ 1 ≤ z 8 ∧ 0 ≤ z 9 ∧ 0 ≤ z 10`.  For a real matrix `M` the
frozen extraction reads `z = extract M`, and the three extra coordinates are *definitionally*

* `z 8  = p M`      (`extract_eight`)
* `z 9  = -M 0 1`   (`extract_nine`, i.e. the model's `e`)
* `z 10 =  M 1 0`   (`extract_ten`, i.e. the model's `beta`)

so the whole question is whether `Qualified (extract M)` and those three inequalities follow
from a proper-B representative.  This module names the residual exactly and proves the
equivalence; `Bridge.lean` pays everything that existing theorems do supply.
-/

noncomputable section

namespace Rho5.Shared.BNormalizationInterface

open Rho5 (Matrix5)
open Rho5.Certificate.B16 (Point Physical)
open Rho5.Certificate.B24Extraction (extract p k r s t)
open Rho5.Certificate.B24MinorBridge (Qualified)
open Rho5.Certificate.B24Reconstruction (HeadBand)
open Rho5.ExternalTailSaturation (LeadingInput ProperB)
open Rho5.ExternalBFibreCapacity (NormalizedB)

/-- **The residual gap, on the matrix.**  The three `NormalizedB` conditions that are *not*
among the fields of `ProperB` or of `LeadingInput`: the fifth pivot is at least one, and the two
top-left corner entries have the signs the B-fibre model expects (`e = -M 0 1 ≥ 0`,
`beta = M 1 0 ≥ 0`).  `ProperB` bounds the pivots `r, s, t, w` and `height` only, so none of the
three is implied by it; `LeadingInput` supplies `0 < p M` and no sign of `M 0 1`, `M 1 0`. -/
def ResidualGap (M : Matrix5) : Prop :=
  1 ≤ p M ∧ M 0 1 ≤ 0 ∧ 0 ≤ M 1 0

/-- The residual read on the extracted point: exactly the three coordinates `NormalizedB` adds
to `Qualified`.  This is the honest form of "the missing part is `1 ≤ z 8`, `0 ≤ z 9`,
`0 ≤ z 10`", with no extra assumption anywhere. -/
theorem residualGap_iff_coords (M : Matrix5) :
    ResidualGap M ↔ 1 ≤ extract M 8 ∧ 0 ≤ extract M 9 ∧ 0 ≤ extract M 10 := by
  rw [ResidualGap]
  rw [Rho5.Certificate.B24Extraction.extract_eight,
      Rho5.Certificate.B24Extraction.extract_nine,
      Rho5.Certificate.B24Extraction.extract_ten]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, neg_nonneg.mpr h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, neg_nonneg.mp h2, h3⟩

/-- Coordinate readings the bridge uses, in one place, so the report and the proof cannot drift
apart: `k`, `r`, `s`, `t`, `p` and the two corner entries of `extract M` are the matrix data. -/
theorem coords_of_extract (M : Matrix5) :
    extract M 0 = k M ∧ extract M 1 = r M ∧ extract M 2 = s M ∧ extract M 3 = t M ∧
      extract M 8 = p M ∧ extract M 9 = -M 0 1 ∧ extract M 10 = M 1 0 :=
  ⟨Rho5.Certificate.B24Extraction.extract_zero M,
   Rho5.Certificate.B24Extraction.extract_one M,
   Rho5.Certificate.B24Extraction.extract_two M,
   Rho5.Certificate.B24Extraction.extract_three M,
   Rho5.Certificate.B24Extraction.extract_eight M,
   Rho5.Certificate.B24Extraction.extract_nine M,
   Rho5.Certificate.B24Extraction.extract_ten M⟩

end Rho5.Shared.BNormalizationInterface
