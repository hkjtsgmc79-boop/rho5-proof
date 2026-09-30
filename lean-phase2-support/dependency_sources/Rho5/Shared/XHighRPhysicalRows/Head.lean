import Rho5.Shared.XHighRSource.DiagramPackets

/-!
# D149 — the real source qualification, and D145's head rows from the actual matrix

D145 left `HeadRows M` (`p - 1 ≤ beta * e ≤ p + 1`) as a hypothesis at the packet entry.  This
module pays it from the **same actual matrix**:

* D119's real head identity `head_eq : p - e * beta = M 1 1` (`Readings.lean`), and
* the frozen normalisation `matrixEntryMax M = 1` of `SatFrame M`, which bounds every entry of `M`
  (`SatFrame.entry_le_one`), hence `|p - e * beta| ≤ 1` (`head_abs_le_one`).

`SourceQual` records this card's exact real qualification: the actual matrix is a `SatFrame M`, the
actual X22 point `extractX M` is in the strict high-`r` domain, and it carries the original high
diagram's core signs `HighRSigns`.  Nothing else is assumed anywhere in the lane.
-/

namespace Rho5.Shared.XHighRPhysicalRows

noncomputable section

open Rho5
open Rho5.Shared.V43MatrixRoundTrip
open Rho5.Shared.XHighRSource

/-- **The real source qualification of D149**: the actual matrix is a `SatFrame`, its actual X22
point is in the strict high-`r` domain of the card, and it carries the high core signs of the
original high diagram.  (`r = k` stays outside the domain, hence low branch.) -/
structure SourceQual (M : M5) : Prop where
  /-- the actual matrix is the frozen normalised complete-pivot frame -/
  sat : SatFrame M
  /-- the actual X22 point lies in `2 < k ≤ 21/10`, `r > k`, `F = height ≥ gamma` -/
  dom : HighRDomain (extractX M)
  /-- the original high diagram's core signs: `A, B ≤ 0 ≤ c, d` -/
  sgn : HighRSigns (extractX M)

/-! ## The real head rows -/

/-- The real head identity, restated at this lane's entry point: `p - e * beta` is the `(1,1)`
entry of the actual matrix. -/
theorem head_eq_entry (M : M5) (h : SatFrame M) : pX M - eX M * betaX M = M 1 1 :=
  head_eq M h.h00

/-- **D145's `HeadRows M` from the actual matrix**: `p - 1 ≤ beta * e ≤ p + 1`.

Paid by the real head identity (`head_eq`) together with the frozen entry bound
`|M 1 1| ≤ 1` of the `SatFrame` normalisation — no head hypothesis is carried any more. -/
theorem headRows_of_satFrame (M : M5) (h : SatFrame M) : HeadRows M := by
  have h1 := head_abs_le_one M h
  obtain ⟨hlo, hhi⟩ := abs_le.mp h1
  refine ⟨?_, ?_⟩
  · nlinarith [hlo]
  · nlinarith [hhi]

/-- The same at the lane's real entry point. -/
theorem headRows_of_source (M : M5) (hs : SourceQual M) : HeadRows M :=
  headRows_of_satFrame M hs.sat

/-! ## Reading the qualification -/

theorem SourceQual.hk (M : M5) (hs : SourceQual M) : 0 < kX M := hs.sat.hk
theorem SourceQual.hp (M : M5) (hs : SourceQual M) : 0 < pX M := hs.sat.hp
theorem SourceQual.hr (M : M5) (hs : SourceQual M) : 0 < rX M := hs.sat.hr

/-- The strict domain, in this lane's coordinates. -/
theorem SourceQual.domain (M : M5) (hs : SourceQual M) :
    2 < kX M ∧ kX M ≤ 21 / 10 ∧ kX M < rX M ∧
      gamma ≤ Rho5.LocalAnalysis.height (extractX M) := by
  simpa only [HighRDomain, extractX_0, extractX_1] using hs.dom

/-- The high core signs, in this lane's coordinates: `A, B ≤ 0 ≤ c, d`. -/
theorem SourceQual.signs (M : M5) (hs : SourceQual M) :
    aX M ≤ 0 ∧ bX M ≤ 0 ∧ 0 ≤ cX M ∧ 0 ≤ dX M := by
  simpa only [HighRSigns, extractX_3, extractX_4, extractX_5, extractX_6] using hs.sgn

/-- The strict domain implies the closed outer box of the two archived high models. -/
theorem SourceQual.closedOuter (M : M5) (hs : SourceQual M) : ClosedOuterBox M :=
  highDomain_closedOuter M hs.dom

end

end Rho5.Shared.XHighRPhysicalRows
