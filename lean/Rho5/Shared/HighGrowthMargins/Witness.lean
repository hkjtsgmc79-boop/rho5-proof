/-
D58 — the corrected D53 canonical witness, with the quantitative margins attached
(card item 5).

Under the explicit hypothesis `4 < rho5Trace`, D53's
`exists_canonical_tail_witness_nonneg` supplies an actual D48 witness `M`, the whole
matrix `N` obtained from it by tail sign normalisation, and the shared value list.  D53
already proved the transport — `p N = p M`, `k N = k M`, `r N = r M`, unchanged growth
ratio and the global comparison — so this file **reuses those equalities** and does not
redo sign or complete-pivot transport.

What is added here: the item 4 package applied to the witness, with the bounds restated
for `N`.  `4 < rho5Trace` remains an assumption of this card; it is never proved, and no
global lower bound above `4` is assumed anywhere.
-/
import Rho5.Shared.HighGrowthMargins.Package
import Rho5.Shared.TailSignNormalization

namespace Rho5.HighGrowthMargins

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **Item 5.**  An actual matrix `N` with nonnegative tail signs, the same global growth
and comparison as the D48 canonical maximiser, and the full set of lower, upper and
product bounds. -/
theorem exists_witness_with_margins (h4 : 4 < Rho5.GrowthSupremum.rho5Trace) :
    ∃ (M N : Matrix5) (values : List ℝ),
      matrixEntryMax N = 1 ∧ N 0 0 = 1 ∧ 0 ≤ s N ∧ 0 ≤ t N ∧
        Rho5.CompletePivotPath.LegalTrace N values ∧
          Rho5.GrowthModel.growthRatio N values = Rho5.GrowthSupremum.rho5Trace ∧
            (∀ N' : Matrix5, N' ≠ 0 → ∀ ws : List ℝ,
              Rho5.CompletePivotPath.LegalTrace N' ws →
                Rho5.GrowthModel.growthRatio N' ws ≤
                  Rho5.GrowthModel.growthRatio N values) ∧
              p N ≤ 2 ∧ k N ≤ 4 ∧ r N ≤ 8 ∧ p N * k N ≤ 4 ∧
                1 / 2 < p N ∧ 1 < k N ∧ 2 < r N ∧
                  1 / 2 < p N * k N ∧ 1 < p N * k N * r N := by
  obtain ⟨M, N, ε, η, values,
    hMmax, -, h00, hlead, hcp0, hcp4, hcp3, -, hpM, hkM, -, -, -, hratio, -, -, -, -,
    -, -, hNdef, hNmax, hN00, hpN, hkN, hrN, hsN, htN, hlegal, hNratio, -, -, -, -,
    hglobal⟩ := Rho5.TailSignNormalization.exists_canonical_tail_witness_nonneg h4
  have hgrowthM : 4 < Rho5.GrowthModel.growthRatio M values := by rw [hratio]; exact h4
  obtain ⟨hpmax, hkmax, hrmax, hpk4, hphalf, hk1, hr2, hpk_half, hpkr_1⟩ :=
    high_growth_package hMmax h00 hlead hgrowthM
  exact ⟨M, N, values, hNmax, hN00, hsN, htN, hlegal, hNratio, hglobal,
    by rw [hpN]; exact hpmax,
    by rw [hkN]; exact hkmax,
    by rw [hrN]; exact hrmax,
    by rw [hpN, hkN]; exact hpk4,
    by rw [hpN]; exact hphalf,
    by rw [hkN]; exact hk1,
    by rw [hrN]; exact hr2,
    by rw [hpN, hkN]; exact hpk_half,
    by rw [hpN, hkN, hrN]; exact hpkr_1⟩

end Rho5.HighGrowthMargins
