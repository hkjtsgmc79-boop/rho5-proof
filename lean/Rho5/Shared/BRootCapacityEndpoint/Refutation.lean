import Rho5.Shared.BRootCapacityEndpoint.Basic

/-!
# D142 — the refutation interface for global super-`alpha` sources

This module states, with the safety premise **explicit and unpaid**, the interface the coordinator
asked for: if every in-root canonical capacity endpoint of this card's kind has height at most
`alpha`, then no `NormalizedB` global super-`alpha` source exists.

The safety premise is deliberately **not** a theorem here:

* it is *not* `rho5Trace = alpha` (nothing in this card claims that),
* it is *not* a whole-root check (no enumeration of root members is performed),
* it is *not* re-derived capacity mathematics (the endpoint's height is D139's `capF`, assembled
  in `Basic.lean`).

The contradiction chain is purely the assembled one:
`alpha < z 23 = y 23 ≤ capF (frameOf y) = canonicalPoint (frameOf y) 23 ≤ alpha`.
-/

namespace Rho5.Shared.BRootCapacityEndpoint

noncomputable section

open Rho5.Certificate.B16 (Point)
open Rho5.Certificate.B24Reconstruction (reconstruct)
open Rho5.ExternalBFibreCapacity
open Rho5.Shared.PaperB17RootEntry (B17Root)

/-- The in-root canonical capacity endpoints of this card's kind: the canonical point of the frame
of a normalized in-root representative. -/
def IsRootCapacityEndpoint (zStar : Point) : Prop :=
  ∃ y : Point, NormalizedB y ∧ B17Root (frameOf y) ∧ zStar = canonicalPoint (frameOf y)

/-- **The explicit, unpaid safety assumption**: every in-root canonical capacity endpoint has
height at most `alpha`. -/
def RootEndpointSafety : Prop :=
  ∀ zStar : Point, IsRootCapacityEndpoint zStar → zStar 23 ≤ Rho5.Algebraic.AlphaRoot.alpha

/-- Under `RootEndpointSafety` there is **no** `NormalizedB` global super-`alpha` source. -/
theorem no_global_super_alpha_source (hsafe : RootEndpointSafety) :
    ¬ ∃ z : Point, NormalizedB z ∧ Rho5.Algebraic.AlphaRoot.alpha < z 23 := by
  rintro ⟨z, hz, hhigh⟩
  obtain ⟨y, hy, hroot, hy23⟩ :=
    Rho5.Shared.PaperB17RootEntry.exists_root_representative z hz hhigh
  have hendpoint : IsRootCapacityEndpoint (canonicalPoint (frameOf y)) := ⟨y, hy, hroot, rfl⟩
  have hs := hsafe _ hendpoint
  have hheight := Rho5.Shared.BFibreGlobalEndpoint.canonical_endpoint_height y hy
  have hge := height_le_capF y hy
  rw [hheight] at hs
  linarith

/-- The same refutation with the safety hypothesis stated directly on representatives (the form a
later card is most likely to discharge): if the canonical endpoint of every normalized in-root
representative has height at most `alpha`, then no `NormalizedB` source exceeds `alpha`. -/
theorem no_global_super_alpha_source_of_representative_bound
    (hsafe : ∀ y : Point, NormalizedB y → B17Root (frameOf y) →
      canonicalPoint (frameOf y) 23 ≤ Rho5.Algebraic.AlphaRoot.alpha) :
    ¬ ∃ z : Point, NormalizedB z ∧ Rho5.Algebraic.AlphaRoot.alpha < z 23 :=
  no_global_super_alpha_source fun zStar hzStar => by
    obtain ⟨y, hy, hroot, rfl⟩ := hzStar
    exact hsafe y hy hroot

/-- The positive direction without the safety premise: a normalized source at the global supremum
with `alpha < rho5Trace` has an in-root, same-height global maximal capacity endpoint. -/
theorem exists_root_capacity_endpoint (z : Point) (h : NormalizedB z)
    (hz : z 23 = Rho5.GrowthSupremum.rho5Trace)
    (hα : Rho5.Algebraic.AlphaRoot.alpha < Rho5.GrowthSupremum.rho5Trace) :
    ∃ zStar : Point,
      IsRootCapacityEndpoint zStar ∧ B17Root (frameOf zStar) ∧ NormalizedB zStar ∧
      zStar 23 = Rho5.GrowthSupremum.rho5Trace ∧
      Rho5.matrixEntryMax (reconstruct zStar) = 1 ∧
      Rho5.MinorCPDomain.PolyCP (reconstruct zStar) ∧
      (∀ w : Point, NormalizedB w → frameOf w = frameOf zStar → w 23 ≤ zStar 23) ∧
      Rho5.GrowthModel.growthRatio (reconstruct zStar) (canonicalPivots (frameOf zStar))
        = Rho5.GrowthSupremum.rho5Trace := by
  obtain ⟨y, zStar, sg, hsg, hmat, hy, hroot, hy23, hy8, hy0, hy1, hy2, hy3, hy9, hy10,
    hstar, hframe, hrootStar, hnorm, hcap, hheight, hentry, hlegal, hpoly, hgrowth, hdom⟩ :=
    root_capacity_endpoint z h hz hα
  subst hstar
  refine ⟨canonicalPoint (frameOf y), ⟨y, hy, hroot, rfl⟩, hrootStar, hnorm, hheight, hentry,
    hpoly, ?_, ?_⟩
  · intro w hw hf
    rw [hframe] at hf
    exact hdom w hw hf
  · rw [hframe]
    exact hgrowth

end

end Rho5.Shared.BRootCapacityEndpoint
