/-
D58 — the combined conditional actual-matrix package (card item 4).

One theorem collects, for an actual normalized matrix in the high-growth domain, both
directions at once:

* the upper bounds from the one-step Schur bound: `p ≤ 2`, `k ≤ 4`, `r ≤ 8`;
* the accepted D54 constraint on the actual leading `3 × 3` block: `p * k ≤ 4`;
* the strict lower margins of item 3: `1/2 < p`, `1 < k`, `2 < r`, and the products
  `1/2 < p * k`, `1 < p * k * r`.

Everything is explicitly conditional: the only hypotheses are D48's high-growth
domain (`matrixEntryMax M = 1`, `M 0 0 = 1`, `LeadingTracePos M values`,
`4 < growthRatio M values`).  Nothing here proves `r ≤ 4`, `4 < rho5Trace`, tail balance
or alpha sharpness.
-/
import Rho5.Shared.HighGrowthMargins.GrowthMargin
import Rho5.Shared.MinorThreeBound

namespace Rho5.HighGrowthMargins

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **Item 4.**  The actual-matrix package in the high-growth domain: upper bounds,
the D54 product constraint, and the strict lower margins with their products. -/
theorem high_growth_package {M : Matrix5} {values : List ℝ}
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M values) :
    p M ≤ 2 ∧ k M ≤ 4 ∧ r M ≤ 8 ∧ p M * k M ≤ 4 ∧
      1 / 2 < p M ∧ 1 < k M ∧ 2 < r M ∧
        1 / 2 < p M * k M ∧ 1 < p M * k M * r M := by
  obtain ⟨hcp0, hcp4, hcp3, -, -, hppos, hkpos, -, -, -, -⟩ :=
    Rho5.CanonicalTail.prefix_structure hM h00 h hgrowth
  obtain ⟨hpmax, hkmax, hrmax⟩ := upper_bounds M h00 hcp0 hcp4 hcp3 hppos hkpos
  have hpk : p M * k M ≤ 4 := Rho5.MinorThreeBound.p_mul_k_le_four M hM h00 hppos hkpos
  obtain ⟨hr2, hk1, hphalf⟩ := strict_margins hM h00 h hgrowth
  exact ⟨hpmax, hkmax, hrmax, hpk, hphalf, hk1, hr2,
    one_half_lt_p_mul_k hphalf hk1, one_lt_p_mul_k_mul_r hphalf hk1 hr2⟩

end Rho5.HighGrowthMargins
