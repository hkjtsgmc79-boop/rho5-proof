import Rho5.Shared.XSmallKSigns.Core
import Rho5.Shared.V43MatrixRoundTrip.Physical

/-!
# D143 stage A — the three real upper bands and the two-branch sign pattern

`DX` (D119) is the actual second Schur block in reverse coordinates:

`DX M 1 1 = r + A*c`, `DX M 1 2 = r + B*c`, `DX M 2 1 = r + A*d`  (`A = aX`, `B = bX`).

The physical band `DX M i j ≤ kX M` therefore gives, with `k < r` from `k_lt_r`:

`A*c ≤ k - r < 0`, `B*c ≤ k - r < 0`, `A*d ≤ k - r < 0`.

Hence `A` and `B` share a sign, `c` and `d` share the opposite sign: exactly the two branches the
paper's legal sign normalization starts from.  No sign is assumed: all three products are paid by
the real band, and the only numeric inputs are `q_* ≤ height M` and `k M ≤ 2`.
-/

noncomputable section

namespace Rho5.Shared.XSmallKSigns

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (k r)
open Rho5.ExternalTailSaturation (height)
open Rho5.Shared.V43MatrixRoundTrip

/-- The third pivot is strictly below the tail pivot on this branch, read in the X coordinates. -/
theorem kX_lt_rX {M : Matrix5} (h : SatFrame M) (hq : qstar ≤ height M)
    (hk2 : k M ≤ 2) : kX M < rX M := by
  have := k_lt_r h hq hk2
  simpa [kX_eq_k, rX_eq_r] using this

/-- First upper band `(1,1)`: `A * c < 0`. -/
theorem aX_mul_cX_neg {M : Matrix5} (h : SatFrame M) (hq : qstar ≤ height M)
    (hk2 : k M ≤ 2) : aX M * cX M < 0 := by
  have hb : rX M + aX M * cX M ≤ kX M := DX_le_kX M h 1 1
  have hlt := kX_lt_rX h hq hk2
  linarith

/-- Second upper band `(1,2)`: `B * c < 0`. -/
theorem bX_mul_cX_neg {M : Matrix5} (h : SatFrame M) (hq : qstar ≤ height M)
    (hk2 : k M ≤ 2) : bX M * cX M < 0 := by
  have hb : rX M + bX M * cX M ≤ kX M := DX_le_kX M h 1 2
  have hlt := kX_lt_rX h hq hk2
  linarith

/-- Third upper band `(2,1)`: `A * d < 0`. -/
theorem aX_mul_dX_neg {M : Matrix5} (h : SatFrame M) (hq : qstar ≤ height M)
    (hk2 : k M ≤ 2) : aX M * dX M < 0 := by
  have hb : rX M + aX M * dX M ≤ kX M := DX_le_kX M h 2 1
  have hlt := kX_lt_rX h hq hk2
  linarith

/-- **The two-branch sign pattern.**  `A`, `B` share a sign and `c`, `d` share the opposite one.
The legal sign normalization only has to decide which of the two branches we are in. -/
theorem sign_dichotomy {M : Matrix5} (hac : aX M * cX M < 0) (hbc : bX M * cX M < 0)
    (had : aX M * dX M < 0) :
    (aX M < 0 ∧ bX M < 0 ∧ 0 < cX M ∧ 0 < dX M) ∨
      (0 < aX M ∧ 0 < bX M ∧ cX M < 0 ∧ dX M < 0) := by
  rcases (mul_neg_iff (a := aX M) (b := cX M)).mp hac with ⟨ha, hc⟩ | ⟨ha, hc⟩
  · have hb : 0 < bX M := by
      rcases (mul_neg_iff (a := bX M) (b := cX M)).mp hbc with ⟨hb, _⟩ | ⟨hb, hc'⟩
      · exact hb
      · exact absurd hc (not_lt.mpr (le_of_lt hc'))
    have hd : dX M < 0 := by
      rcases (mul_neg_iff (a := aX M) (b := dX M)).mp had with ⟨_, hd⟩ | ⟨ha', _⟩
      · exact hd
      · exact absurd ha (not_lt.mpr (le_of_lt ha'))
    exact Or.inr ⟨ha, hb, hc, hd⟩
  · have hb : bX M < 0 := by
      rcases (mul_neg_iff (a := bX M) (b := cX M)).mp hbc with ⟨hb, hc'⟩ | ⟨hb, _⟩
      · exact absurd hc (not_lt.mpr (le_of_lt hc'))
      · exact hb
    have hd : 0 < dX M := by
      rcases (mul_neg_iff (a := aX M) (b := dX M)).mp had with ⟨ha', _⟩ | ⟨_, hd⟩
      · exact absurd ha' (not_lt.mpr (le_of_lt ha))
      · exact hd
    exact Or.inl ⟨ha, hb, hc, hd⟩

end Rho5.Shared.XSmallKSigns
