/-
D67 — the actual signed minors `A`, `B`, `C`, `D` and their readings.

The card's notation for an actual normalized matrix `M`:

| symbol | value | role |
| --- | --- | --- |
| `A M` | `m2 M 0 0 = p M` | leading signed `2 × 2` minor (D61) |
| `B M` | `m3 M 0 0 = p M * k M` | leading signed `3 × 3` minor (D61) |
| `C M` | `m4 M 0 0 = p M * k M * r M` | leading signed `4 × 4` bordered minor (D62 stage A) |
| `D M` | `M.det` | signed determinant of the original matrix |

They are the *actual* original-matrix minors: no new minor family is introduced, and
D62's `PolyCP` is not touched.  The readings reuse the paid identities of D61, D62 and
D56; only positive denominators are assumed (the card's `p, k, r > 0`).
-/
import Rho5.Shared.PrefixBorderedMinors
import Rho5.Shared.MinorCPDomain
import Rho5.Shared.TailDeterminant
import Rho5.Shared.HighGrowthMargins
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Rho5.MinorGrowthThreshold

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-! ## 1. The four signed minors -/

/-- The leading signed `2 × 2` minor, i.e. D61's `m2 M 0 0`. -/
noncomputable def A (M : Matrix5) : ℝ := Rho5.PrefixBorderedMinors.m2 M 0 0

/-- The leading signed `3 × 3` minor, i.e. D61's `m3 M 0 0`. -/
noncomputable def B (M : Matrix5) : ℝ := Rho5.PrefixBorderedMinors.m3 M 0 0

/-- The leading signed `4 × 4` bordered minor, i.e. D62's `m4 M 0 0`. -/
noncomputable def C (M : Matrix5) : ℝ := Rho5.MinorCPDomain.m4 M 0 0

/-- The signed determinant of the original matrix. -/
noncomputable def D (M : Matrix5) : ℝ := M.det

/-! ## 2. Readings through the paid identities -/

/-- `A M = p M` (D61's `m2_zero_zero`, needs `M 0 0 = 1`). -/
theorem A_eq (M : Matrix5) (h00 : M 0 0 = 1) : A M = p M :=
  Rho5.PrefixBorderedMinors.m2_zero_zero M h00

/-- `B M = p M * k M` (D61's `m3_zero_zero`, needs `M 0 0 = 1` and `p M ≠ 0`). -/
theorem B_eq (M : Matrix5) (h00 : M 0 0 = 1) (hp : p M ≠ 0) : B M = p M * k M :=
  Rho5.PrefixBorderedMinors.m3_zero_zero M h00 hp

/-- `C M = p M * k M * r M` (D62 stage A's `m4_00_eq`). -/
theorem C_eq (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    C M = p M * k M * r M :=
  Rho5.MinorCPDomain.m4_00_eq M h00 hp hk

/-- `D M` is the determinant by definition. -/
theorem D_eq (M : Matrix5) : D M = M.det := rfl

/-! ## 3. Positivity and the two quotient identities -/

/-- **`B M > 0`** from the paid reading and `p, k > 0`. -/
theorem B_pos (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) : 0 < B M := by
  rw [B_eq M h00 (ne_of_gt hp)]
  exact mul_pos hp hk

/-- **`C M > 0`** from the paid reading and `p, k, r > 0`. -/
theorem C_pos (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hr : 0 < r M) : 0 < C M := by
  rw [C_eq M h00 hp hk]
  exact mul_pos (mul_pos hp hk) hr

/-- **`C M = r M * B M`** — the exact multiplicative form of the third pivot. -/
theorem C_eq_r_mul_B (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    C M = r M * B M := by
  rw [C_eq M h00 hp hk, B_eq M h00 (ne_of_gt hp)]
  ring

/-- **`r M = C M / B M`** (dividing by the positive denominator `B M`). -/
theorem r_eq_C_div_B (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    r M = C M / B M := by
  rw [C_eq_r_mul_B M h00 hp hk,
    mul_div_cancel_right₀ _ (ne_of_gt (B_pos M h00 hp hk))]

/-- **`delta M = D M / C M`** (D56's signed determinant identity, positive denominator). -/
theorem delta_eq_D_div_C (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hr : 0 < r M) : Rho5.CanonicalTail.delta M = D M / C M := by
  rw [D, C_eq M h00 hp hk]
  exact Rho5.TailDeterminant.delta_eq_det_div M h00 (ne_of_gt hp) (ne_of_gt hk) (ne_of_gt hr)

/-- **`|D M| = |delta M| * C M`** — the absolute determinant through the positive
denominator, used by both directions of the threshold equivalence. -/
theorem abs_D_eq_abs_delta_mul_C (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hk : 0 < k M) (hr : 0 < r M) :
    |D M| = |Rho5.CanonicalTail.delta M| * C M := by
  have hC : 0 < C M := C_pos M h00 hp hk hr
  rw [delta_eq_D_div_C M h00 hp hk hr, abs_div, abs_of_pos hC,
    div_mul_cancel₀ _ (ne_of_gt hC)]

end Rho5.MinorGrowthThreshold
