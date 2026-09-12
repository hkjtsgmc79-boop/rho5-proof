import Rho5.Shared.BorderedTailMinors

/-!
# D62 stage A — the actual tail complete pivot paid by the four bordered minors

The card fixes four `4 × 4` bordered minors of the actual matrix,
`m4_ij = det (borderedMinor M i j)` (D52's fixed embedding, deleting row `4 - i` and
column `4 - j`), with `C = m4_00`.  This file proves, for the actual whole matrix with
`M 0 0 = 1` and `p, k, r > 0`:

* the D52 identity `m4_ij = p M * k M * T2 M i j` (no division), and therefore
  `C = m4_00 = p M * k M * r M` and the four explicit readings;
* the **actual tail complete-pivot qualification** `IsCompletePivot (T2 M) 0 0` holds
  **iff** all four bordered minors are bounded by `C`:
  `∀ i j : Fin 2, |m4 M i j| ≤ m4 M 0 0`.

The equivalence is exactly the positivity scaling `p M * k M > 0` applied to D52's
identity; it is an actual fixed-tail equivalence, not a generic rational-inequality
library.  No division by `T2` or by `r` appears: the only denominator ever used is the
*proved positive* product `p M * k M`, and `r M > 0` is used only to remove the absolute
value of the tail pivot.  The polynomial side is not claimed here — stage B (D61's
`m2`/`m3` plus these `m4`) is gated on `PREFIX_MINORS_READY.json`.
-/

namespace Rho5.MinorCPDomain

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)
open Rho5.Pivot (IsCompletePivot)

/-! ## 1. The four bordered minors as determinants -/

/-- **The card's `m4`.**  The determinant of the `4 × 4` bordered minor obtained by
deleting row `4 - i` and column `4 - j`. -/
noncomputable def m4 (M : Matrix5) (i j : Fin 2) : ℝ :=
  (Rho5.BorderedTailMinors.borderedMinor M i j).det

theorem m4_apply (M : Matrix5) (i j : Fin 2) :
    m4 M i j = (Rho5.BorderedTailMinors.borderedMinor M i j).det := rfl

/-- **D52's division-free identity**, transported to `m4`. -/
theorem m4_eq (M : Matrix5) (i j : Fin 2) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    m4 M i j = p M * k M * T2 M i j := by
  rw [m4, Rho5.BorderedTailMinors.det_borderedMinor M i j h00 (ne_of_gt hp) (ne_of_gt hk)]

/-- **The card's `C = p * k * r`.** -/
theorem m4_00_eq (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    m4 M 0 0 = p M * k M * r M := by
  rw [m4, Rho5.BorderedTailMinors.det_borderedMinor_00 M h00 (ne_of_gt hp) (ne_of_gt hk)]

/-- The upper-right reading `m4_01 = p * k * s`. -/
theorem m4_01_eq (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    m4 M 0 1 = p M * k M * s M := by
  rw [m4, Rho5.BorderedTailMinors.det_borderedMinor_01 M h00 (ne_of_gt hp) (ne_of_gt hk)]

/-- The lower-left reading `m4_10 = p * k * t`. -/
theorem m4_10_eq (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    m4 M 1 0 = p M * k M * t M := by
  rw [m4, Rho5.BorderedTailMinors.det_borderedMinor_10 M h00 (ne_of_gt hp) (ne_of_gt hk)]

/-- The lower-right reading `m4_11 = p * k * (T2 M 1 1)` (the `d` of the tail). -/
theorem m4_11_eq (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    m4 M 1 1 = p M * k M * T2 M 1 1 :=
  m4_eq M 1 1 h00 hp hk

/-! ## 2. Positivity scaling without division -/

/-- For a *proved* positive factor `c`, the two absolute-value bounds are equivalent;
this is the only step that "cancels" `p * k`, and it is a `mul_le_mul_left` with an
explicit positivity hypothesis, not a division. -/
theorem abs_mul_le_mul_iff (c x y : ℝ) (hc : 0 < c) : |c * x| ≤ c * y ↔ |x| ≤ y := by
  rw [abs_mul, abs_of_pos hc]
  exact ⟨fun h => le_of_mul_le_mul_left h hc, fun h => mul_le_mul_of_nonneg_left h hc.le⟩

/-- The tail pivot absolute value, without any denominator: `|T2 M 0 0| = r M`. -/
theorem abs_T2_zero_zero (M : Matrix5) (hr : 0 < r M) : |T2 M 0 0| = r M := by
  rw [r]
  exact abs_of_pos hr

/-! ## 3. Stage A main equivalence -/

/-- **Stage A (the card's statement).**  For the actual whole matrix with `M 0 0 = 1` and
`p, k, r > 0`, the actual tail leading complete pivot is *equivalent* to the four bordered
minors being bounded by `C = m4_00`.

Both directions are proved from D52's identity `m4 = p * k * T2` and the *established*
positivity `p * k > 0`; the `r > 0` hypothesis is used only to write `|T2 M 0 0| = r M`. -/
theorem tail_cp_iff_minors (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hr : 0 < r M) :
    IsCompletePivot (T2 M) 0 0 ↔ ∀ i j : Fin 2, |m4 M i j| ≤ m4 M 0 0 := by
  have hck : 0 < p M * k M := mul_pos hp hk
  have hr' : |T2 M 0 0| = r M := abs_T2_zero_zero M hr
  constructor
  · intro hcp i j
    have h := hcp i j
    rw [hr'] at h
    rw [m4_eq M i j h00 hp hk, m4_00_eq M h00 hp hk]
    exact (abs_mul_le_mul_iff (p M * k M) (T2 M i j) (r M) hck).mpr h
  · intro h i j
    have h' := h i j
    rw [m4_eq M i j h00 hp hk, m4_00_eq M h00 hp hk] at h'
    have h'' := (abs_mul_le_mul_iff (p M * k M) (T2 M i j) (r M) hck).mp h'
    rwa [hr']

/-- The same equivalence with the bound written through the D37 readings of the four
minors, i.e. the four explicit inequalities
`|p*k*r| ≤ p*k*r`, `|p*k*s| ≤ p*k*r`, `|p*k*t| ≤ p*k*r`, `|p*k*(T2 M 1 1)| ≤ p*k*r`. -/
theorem tail_cp_iff_readings (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hr : 0 < r M) :
    IsCompletePivot (T2 M) 0 0 ↔
      |p M * k M * r M| ≤ p M * k M * r M ∧
      |p M * k M * s M| ≤ p M * k M * r M ∧
      |p M * k M * t M| ≤ p M * k M * r M ∧
      |p M * k M * T2 M 1 1| ≤ p M * k M * r M := by
  have e00 : m4 M 0 0 = p M * k M * r M := m4_00_eq M h00 hp hk
  have e01 : m4 M 0 1 = p M * k M * s M := m4_01_eq M h00 hp hk
  have e10 : m4 M 1 0 = p M * k M * t M := m4_10_eq M h00 hp hk
  have e11 : m4 M 1 1 = p M * k M * T2 M 1 1 := m4_11_eq M h00 hp hk
  rw [tail_cp_iff_minors M h00 hp hk hr]
  constructor
  · intro h
    exact ⟨by simpa [e00] using h 0 0, by simpa [e01, e00] using h 0 1,
      by simpa [e10, e00] using h 1 0, by simpa [e11, e00] using h 1 1⟩
  · rintro ⟨h1, h2, h3, h4⟩ i j
    fin_cases i <;> fin_cases j
    · show |m4 M 0 0| ≤ m4 M 0 0
      simpa [e00] using h1
    · show |m4 M 0 1| ≤ m4 M 0 0
      simpa [e01, e00] using h2
    · show |m4 M 1 0| ≤ m4 M 0 0
      simpa [e10, e00] using h3
    · show |m4 M 1 1| ≤ m4 M 0 0
      simpa [e11, e00] using h4

end Rho5.MinorCPDomain
