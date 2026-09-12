import Rho5.Shared.PaperB17RootEntry.Entry
import Rho5.Shared.BFibreGlobalEndpoint

/-!
# D142 — the in-root canonical capacity endpoint of a normalized super-`alpha` source

Assembly over two accepted layers, with no re-proof of either:

* **D134 / G05** (`Rho5.Shared.PaperB17RootEntry.high_normalizedB_has_canonical_root_representative`):
  a `NormalizedB z` with `alpha < z 23` has a **same-height real sign representative** `y` — a
  genuine legal row/column sign operation (`sg i = ±1` and
  `reconstruct y i j = sg i * reconstruct z i j * sg j`), with `NormalizedB y`,
  `B17Root (frameOf y)` and all the preserved readings (`y 23 = z 23`, `y 8 = z 8`, `y 0 = z 0`,
  `y 1 = z 1`, `y 2 = z 2`, `y 3 = z 3`, `y 9 = z 9`, `y 10 = z 10`);
* **D139** (`Rho5.Shared.BFibreGlobalEndpoint`): at `y`'s own frame the canonical point
  `canonicalPoint (frameOf y)` has height `capF (frameOf y)`, the same frame, actual growth
  `capF`, a legal trace, `PolyCP` and entry max `1`, and it dominates the whole fibre of that
  frame.

Composing them gives the card's endpoint `zStar := canonicalPoint (frameOf y)`:

* it is **in-root**: `frameOf zStar = frameOf y` (D139's frame invariance pays root invariance,
  `B17Root (frameOf zStar)`), and `NormalizedB zStar`;
* it is **same-height**: `zStar 23 = capF (frameOf y) = rho5Trace = z 23`;
* it is the **global maximum**: `growthRatio (reconstruct zStar) (canonicalPivots (frameOf y)) = rho5Trace`
  and every `NormalizedB w` with `frameOf w = frameOf y` has `w 23 ≤ zStar 23`;
* the **real relations are preserved exactly as they are**: the source relation `z → y` is the
  sign relation above, and `y → zStar` is the *same-frame* relation
  `frameOf zStar = frameOf y`.

**What is deliberately NOT claimed**: `zStar` is *not* claimed to be a sign transform of the
original matrix `reconstruct z`.  The capacity endpoint is the canonical point of the frame, whose
head coordinates are the capacity-optimal ones
(`zStar 10 = betaBar (frameOf y)`, `zStar 8 = prefixP (frameOf y)`, `zStar 9 = prefixE (frameOf y)`,
`zStar 1 = R`, `zStar 2 = min R sUpper`, `zStar 3 = min R tUpper` — D121's `canonical_coordinates`);
capacity optimisation may change the head, so only the `z → y` sign relation and the `y → zStar`
same-frame relation are asserted.
-/

namespace Rho5.Shared.BRootCapacityEndpoint

noncomputable section

open Rho5.Certificate.B16 (Point)
open Rho5.Certificate.B24Reconstruction (reconstruct)
open Rho5.ExternalBFibreCapacity
open Rho5.Shared.PaperB17RootEntry (B17Root)

/-- **The in-root canonical capacity endpoint.**  For a normalized source whose height is the
global supremum `rho5Trace`, with `alpha < rho5Trace`, there is a same-height real sign
representative `y` in the complete 17-dimensional closed root, and the canonical point of `y`'s
own frame is a normalized, in-root, same-height global maximal capacity endpoint with an actual
legal trace, `PolyCP`, entry max `1` and actual growth equal to `rho5Trace`. -/
theorem root_capacity_endpoint (z : Point) (h : NormalizedB z)
    (hz : z 23 = Rho5.GrowthSupremum.rho5Trace)
    (hα : Rho5.Algebraic.AlphaRoot.alpha < Rho5.GrowthSupremum.rho5Trace) :
    ∃ y zStar : Point, ∃ sg : Fin 5 → ℝ,
      (∀ i : Fin 5, sg i = 1 ∨ sg i = -1) ∧
      (∀ i j : Fin 5, reconstruct y i j = sg i * reconstruct z i j * sg j) ∧
      NormalizedB y ∧ B17Root (frameOf y) ∧
      y 23 = z 23 ∧ y 8 = z 8 ∧ y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = z 2 ∧ y 3 = z 3 ∧
      y 9 = z 9 ∧ y 10 = z 10 ∧
      zStar = canonicalPoint (frameOf y) ∧
      frameOf zStar = frameOf y ∧ B17Root (frameOf zStar) ∧ NormalizedB zStar ∧
      capF (frameOf y) = Rho5.GrowthSupremum.rho5Trace ∧
      zStar 23 = Rho5.GrowthSupremum.rho5Trace ∧
      Rho5.matrixEntryMax (reconstruct zStar) = 1 ∧
      Rho5.CompletePivotPath.LegalTrace (reconstruct zStar) (canonicalPivots (frameOf y)) ∧
      Rho5.MinorCPDomain.PolyCP (reconstruct zStar) ∧
      Rho5.GrowthModel.growthRatio (reconstruct zStar) (canonicalPivots (frameOf y))
        = Rho5.GrowthSupremum.rho5Trace ∧
      (∀ w : Point, NormalizedB w → frameOf w = frameOf y → w 23 ≤ zStar 23) := by
  have hzα : Rho5.Algebraic.AlphaRoot.alpha < z 23 := by rw [hz]; exact hα
  obtain ⟨y, sg, hsg, hmat, hy, hroot, hy23, hy8, hy0, hy1, hy2, hy3, hy9, hy10⟩ :=
    Rho5.Shared.PaperB17RootEntry.high_normalizedB_has_canonical_root_representative z h hzα
  have hyρ : y 23 = Rho5.GrowthSupremum.rho5Trace := by rw [hy23, hz]
  have hcap := Rho5.Shared.BFibreGlobalEndpoint.capF_eq_rho5Trace y hy hyρ
  have hframe := Rho5.Shared.BFibreGlobalEndpoint.canonical_endpoint_frame y hy
  have hnorm := Rho5.Shared.BFibreGlobalEndpoint.canonical_endpoint_normalized y hy
  have hheight := Rho5.Shared.BFibreGlobalEndpoint.canonical_endpoint_height y hy
  have hmat' := Rho5.Shared.BFibreGlobalEndpoint.canonical_endpoint_matrix y hy
  have hgrowth := Rho5.Shared.BFibreGlobalEndpoint.global_max_growth_eq_rho5Trace y hy hyρ
  have hdom := Rho5.Shared.BFibreGlobalEndpoint.canonical_endpoint_dominates y hy
  exact ⟨y, canonicalPoint (frameOf y), sg, hsg, hmat, hy, hroot, hy23, hy8, hy0, hy1, hy2, hy3,
    hy9, hy10, rfl, hframe, by rw [hframe]; exact hroot, hnorm, hcap, by rw [hheight, hcap],
    hmat'.1, hmat'.2.1, hmat'.2.2.1, hgrowth, hdom⟩

/-- The endpoint's head is the capacity-optimal head of its frame (D121'
`canonical_coordinates`), **not** necessarily the head of the sign representative `y` — this is
exactly why no sign relation between `z` and the capacity endpoint is asserted. -/
theorem root_endpoint_head_readings (y : Point) :
    canonicalPoint (frameOf y) 10 = betaBar (frameOf y) ∧
    canonicalPoint (frameOf y) 8 = prefixP (frameOf y) ∧
    canonicalPoint (frameOf y) 9 = prefixE (frameOf y) ∧
    canonicalPoint (frameOf y) 1
      = (tailLimits (frameOf y) (prefixP (frameOf y))).R ∧
    canonicalPoint (frameOf y) 2
      = min (tailLimits (frameOf y) (prefixP (frameOf y))).R
          (tailLimits (frameOf y) (prefixP (frameOf y))).sUpper ∧
    canonicalPoint (frameOf y) 3
      = min (tailLimits (frameOf y) (prefixP (frameOf y))).R
          (tailLimits (frameOf y) (prefixP (frameOf y))).tUpper ∧
    canonicalPoint (frameOf y) 23 = capF (frameOf y) :=
  canonical_coordinates (frameOf y)

end

end Rho5.Shared.BRootCapacityEndpoint
