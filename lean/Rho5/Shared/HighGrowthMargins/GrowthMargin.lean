/-
D58 — growth-ratio margins in the actual high-growth domain.

The card's items 2 and 3: writing `g = growthRatio M values` for the actual D48
high-growth configuration, the paid tail bound gives `g ≤ 2 * r M`, hence

    g / 2 ≤ r M,    g / 4 ≤ k M,    g / 8 ≤ p M,

and under the explicit hypothesis `4 < g` the uniform strict margins

    2 < r M,    1 < k M,    1/2 < p M,    1/2 < p M * k M,    1 < p M * k M * r M.

`g ≤ 2 * r M` is D48's tail envelope `g ≤ r + |s * t| / r` combined with D46's
complete-pivot envelope bound `E ≤ 2 * r`; the chain to `p` uses the one-step bounds of
`HighGrowthMargins/OneStep.lean`.  Every hypothesis D48 needs is kept explicit — in
particular `4 < g` is an assumption here, never derived from a global lower bound.
-/
import Rho5.Shared.HighGrowthMargins.OneStep
import Rho5.Shared.CanonicalTail
import Rho5.Shared.TailEnvelope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Rho5.HighGrowthMargins

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-! ## 2. The tail bound `g ≤ 2 * r` and the three margins -/

/-- **Item 2 (the paid tail bound).**  In the high-growth domain the actual growth ratio
is at most twice the third pivot: D48's envelope `g ≤ r + |s t| / r` and D46's
complete-pivot bound `r + |s t| / r ≤ 2 r`. -/
theorem growthRatio_le_two_mul_r {M : Matrix5} {values : List ℝ}
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M values) :
    Rho5.GrowthModel.growthRatio M values ≤ 2 * r M := by
  have henv := Rho5.CanonicalTail.growthRatio_le_tailEnvelope hM h00 h hgrowth
  obtain ⟨-, -, -, hcpT2, -, -, -, hrpos, -, -, -⟩ :=
    Rho5.CanonicalTail.prefix_structure hM h00 h hgrowth
  have h2 : r M + |s M * t M| / r M ≤ 2 * r M :=
    Rho5.TailEnvelope.envelope_le_two_mul_of_isCompletePivot_pos hcpT2 hrpos
  exact henv.trans h2

/-- **Item 2 (`g / 2 ≤ r`).** -/
theorem growthRatio_div_two_le_r {M : Matrix5} {values : List ℝ}
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M values) :
    Rho5.GrowthModel.growthRatio M values / 2 ≤ r M := by
  have hle := growthRatio_le_two_mul_r hM h00 h hgrowth
  linarith

/-- **Item 2 (`g / 4 ≤ k`).** -/
theorem growthRatio_div_four_le_k {M : Matrix5} {values : List ℝ}
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M values) :
    Rho5.GrowthModel.growthRatio M values / 4 ≤ k M := by
  obtain ⟨-, -, hcp3, -, -, -, hkpos, -, -, -, -⟩ :=
    Rho5.CanonicalTail.prefix_structure hM h00 h hgrowth
  have h1 := growthRatio_le_two_mul_r hM h00 h hgrowth
  have h2 := r_le_two_mul_k M hcp3 hkpos
  linarith

/-- **Item 2 (`g / 8 ≤ p`).** -/
theorem growthRatio_div_eight_le_p {M : Matrix5} {values : List ℝ}
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M values) :
    Rho5.GrowthModel.growthRatio M values / 8 ≤ p M := by
  obtain ⟨-, hcp4, hcp3, -, -, hppos, hkpos, -, -, -, -⟩ :=
    Rho5.CanonicalTail.prefix_structure hM h00 h hgrowth
  have h1 := growthRatio_le_two_mul_r hM h00 h hgrowth
  have h2 := r_le_two_mul_k M hcp3 hkpos
  have h3 := k_le_two_mul_p M hcp4 hppos
  linarith

/-- **Item 2 (chained form).**  `g ≤ 8 * p`, the single inequality behind the three
divided margins. -/
theorem growthRatio_le_eight_mul_p {M : Matrix5} {values : List ℝ}
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M values) :
    Rho5.GrowthModel.growthRatio M values ≤ 8 * p M := by
  have h1 := growthRatio_le_two_mul_r hM h00 h hgrowth
  have h2 := growthRatio_div_four_le_k hM h00 h hgrowth
  have h3 := growthRatio_div_eight_le_p hM h00 h hgrowth
  linarith

/-! ## 3. The strict margins under `4 < g` -/

/-- **Item 3 (uniform strict margins).**  Under the explicit hypothesis `4 < g` the
three leading pivots are strictly above `2`, `1` and `1/2`. -/
theorem strict_margins {M : Matrix5} {values : List ℝ}
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M values) :
    2 < r M ∧ 1 < k M ∧ 1 / 2 < p M := by
  have h1 := growthRatio_div_two_le_r hM h00 h hgrowth
  have h2 := growthRatio_div_four_le_k hM h00 h hgrowth
  have h3 := growthRatio_div_eight_le_p hM h00 h hgrowth
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- **Item 3 (`p * k > 1/2`).**  Positivity of `k` is used, not assumed away: `1 < k`
supplies it. -/
theorem one_half_lt_p_mul_k {p k : ℝ} (hp : 1 / 2 < p) (hk : 1 < k) : 1 / 2 < p * k := by
  nlinarith

/-- **Item 3 (`p * k * r > 1`).** -/
theorem one_lt_p_mul_k_mul_r {p k r : ℝ} (hp : 1 / 2 < p) (hk : 1 < k) (hr : 2 < r) :
    1 < p * k * r := by
  nlinarith [mul_pos (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hp)
    (lt_trans (by norm_num : (0 : ℝ) < 1) hk)]

end Rho5.HighGrowthMargins
