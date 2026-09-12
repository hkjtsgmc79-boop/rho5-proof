/-
D58 — one-step quantitative pivot bounds in the actual high-growth domain.

The card's item 1: for an actual normalized matrix whose leading first four pivots are
complete, the first three pivots satisfy

    p M ≤ 2,    k M ≤ 2 * p M,    r M ≤ 2 * k M.

These are the **actual** one-step consequences of D15's complete-pivot Schur bound
(`Rho5.TraceGrowth.pivotSchur_entry_abs_le_two_mul_pivot`): a complete pivot is the
global entry maximum, so the Schur complement's entries are bounded by `2 * |pivot|`,
and each successive pivot is one entry of the previous update.  No arbitrary-dimension
coarse growth theory is reproved here — the frozen D15 theorem is used as is, and the
`IsCompletePivot` hypotheses are supplied explicitly by the caller (D48's
`prefix_structure` discharges them in the high-growth domain).
-/
import Rho5.Shared.TraceGrowth
import Rho5.Shared.MatrixNormalization
import Rho5.Certificate.B24Extraction.Extract
import Mathlib.Tactic.Linarith

namespace Rho5.HighGrowthMargins

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-! ## 1. The three one-step bounds -/

/-- **Item 1 (`p ≤ 2`).**  The first pivot is the `(0,0)` entry of the first Schur
update, every entry of which is bounded by `2 * |M 0 0| = 2`. -/
theorem p_le_two (M : Matrix5) (h00 : M 0 0 = 1)
    (hcp : Rho5.Pivot.IsCompletePivot M 0 0) : p M ≤ 2 := by
  have hne : M 0 0 ≠ 0 := by rw [h00]; norm_num
  have h := Rho5.TraceGrowth.pivotSchur_entry_abs_le_two_mul_pivot M 0 0 hcp hne 0 0
  have h' : |p M| ≤ 2 * |M 0 0| := by
    rwa [show Rho5.PivotReindex.pivotSchur M 0 0 0 0 = p M from rfl] at h
  rw [h00, abs_one, mul_one] at h'
  exact (le_abs_self (p M)).trans h'

/-- **Item 1 (`k ≤ 2 * p`).**  The second pivot is an entry of the second Schur update
of a matrix whose complete pivot is `p M`. -/
theorem k_le_two_mul_p (M : Matrix5) (hcp : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hp : 0 < p M) : k M ≤ 2 * p M := by
  have hne : S4 M 0 0 ≠ 0 := ne_of_gt hp
  have h := Rho5.TraceGrowth.pivotSchur_entry_abs_le_two_mul_pivot (S4 M) 0 0 hcp hne 0 0
  have h' : |k M| ≤ 2 * p M := by
    rw [show Rho5.PivotReindex.pivotSchur (S4 M) 0 0 0 0 = k M from rfl,
      show (S4 M 0 0) = p M from rfl, abs_of_pos hp] at h
    exact h
  exact (le_abs_self (k M)).trans h'

/-- **Item 1 (`r ≤ 2 * k`).**  The third pivot is an entry of the third Schur update of
a matrix whose complete pivot is `k M`. -/
theorem r_le_two_mul_k (M : Matrix5) (hcp : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hk : 0 < k M) : r M ≤ 2 * k M := by
  have hne : S3 M 0 0 ≠ 0 := ne_of_gt hk
  have h := Rho5.TraceGrowth.pivotSchur_entry_abs_le_two_mul_pivot (S3 M) 0 0 hcp hne 0 0
  have h' : |r M| ≤ 2 * k M := by
    rw [show Rho5.PivotReindex.pivotSchur (S3 M) 0 0 0 0 = r M from rfl,
      show (S3 M 0 0) = k M from rfl, abs_of_pos hk] at h
    exact h
  exact (le_abs_self (r M)).trans h'

/-- **Item 1, upper bounds.**  Chaining the three one-step bounds gives `k M ≤ 4` and
`r M ≤ 8` under the same hypotheses. -/
theorem upper_bounds (M : Matrix5) (h00 : M 0 0 = 1)
    (hcp0 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) :
    p M ≤ 2 ∧ k M ≤ 4 ∧ r M ≤ 8 := by
  have h1 := p_le_two M h00 hcp0
  have h2 := k_le_two_mul_p M hcp4 hp
  have h3 := r_le_two_mul_k M hcp3 hk
  refine ⟨h1, ?_, ?_⟩
  · linarith
  · linarith

end Rho5.HighGrowthMargins
