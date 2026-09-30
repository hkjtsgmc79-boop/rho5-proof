import Rho5.Shared.XHighRSource.Defs

/-!
# D145 — `F = height`, and why the `2r` reading is a different quantity

The high-value reading of the V34 high branch is the frozen height `r - w` (D119 keeps the free
`w = T2 M 1 1`).  `TS.F = 2r` is **not** this quantity: the two agree exactly when `w = -r`.
-/

namespace Rho5.Shared.XHighRSource

noncomputable section

open Rho5
open Rho5.Shared.V43MatrixRoundTrip

/-- **`F = height = r - w` on the actual X22 point** (not `2r`). -/
theorem height_extractX_eq (M : M5) :
    Rho5.LocalAnalysis.height (extractX M) = rX M - wX M := by
  simp [Rho5.LocalAnalysis.height]

/-- The `2r` reading coincides with the height **only** when `w = -r`. -/
theorem two_r_eq_height_iff (M : M5) :
    2 * rX M = Rho5.LocalAnalysis.height (extractX M) ↔ wX M = -(rX M) := by
  rw [height_extractX_eq]
  constructor <;> intro h <;> linarith

/-- The high-value threshold, transported to the actual coordinates. -/
theorem gamma_le_height_iff (M : M5) :
    gamma ≤ Rho5.LocalAnalysis.height (extractX M) ↔ gamma ≤ rX M - wX M := by
  rw [height_extractX_eq]

/-- The domain membership of the actual point, from the coordinate premises. -/
theorem extractX_highDomain (M : M5) (h2 : 2 < kX M) (hJ : kX M ≤ 21 / 10)
    (hr : kX M < rX M) (hF : gamma ≤ rX M - wX M) :
    HighRDomain (extractX M) := by
  refine ⟨h2, hJ, hr, ?_⟩
  rw [gamma_le_height_iff]
  exact hF

/-- The actual domain sits inside the models' closed outer box. -/
theorem highDomain_subset_closed (x : X) (h : HighRDomain x) : HighRClosedDomain x :=
  ⟨le_of_lt h.1, h.2.1, le_of_lt h.2.2.1, h.2.2.2⟩

/-- `r = k` sources are **low branch**: they are not in the strict high-r domain. -/
theorem not_highR_of_r_eq_k (x : X) (h : x 1 = x 0) : ¬ HighRDomain x :=
  fun hd => absurd (hd.2.2.1) (by rw [h]; exact lt_irrefl _)

end

end Rho5.Shared.XHighRSource
