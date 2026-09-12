import Rho5.Certificate.B24Trace.Steps
import Mathlib.Tactic.FinCases

/-!
# D33 / B24Trace — legality of the last three steps

The card lists the conditions that pay for the last three complete pivots:

`Physical z`, the head band `HeadBand z`, `0 < p z`, `0 < z 0`, `0 ≤ z 2`,
`z 2 ≤ z 1`, `0 ≤ z 3` — with `Physical` already supplying `r = z 1 > 0` and
`t = z 3 ≤ r`.

Each of the three pivots is shown to be a **complete** pivot *and* non-zero:

* step 3 on `D z`: `d_bound` gives `|D_ij| ≤ k` and the pivot entry is `k = z 0`;
* step 4 on `[[r, s], [t, -r]]`: the pivot entry is `r`, and `|s| ≤ r`, `|t| ≤ r`
  come from `0 ≤ s`, `s ≤ r`, `0 ≤ t`, `t ≤ r`;
* step 5 on the `1 × 1` tail: completeness is trivial, and the entry is `-z 23` with
  `z 23 > 0` (`F_pos`), so the pivot does not vanish.

Nothing here is a new predicate field: `IsCompletePivot` is the frozen D10/pilot
predicate and the non-vanishing is a plain `≠ 0` statement.  In particular the
legality conclusions are **not** assumed anywhere.
-/

namespace Rho5.Certificate.B24Trace

open Rho5.Certificate.B16 (Point D O S L P u xv v q Physical)
open Rho5.Certificate.B24Reconstruction (reconstruct firstStage p HeadBand)

/-! ## Step 3 on the `3 × 3` core -/

/-- **Item 2 (step 3 legality).**  `0 < k` makes `(0, 0)` a complete pivot of `D z`:
the frozen `Physical.d_bound` gives `|D_ij| ≤ k` and the pivot entry is `k`. -/
theorem isCompletePivot_D_zero_zero (z : Point) (hz : Physical z) (hk : 0 < z 0) :
    Rho5.Pivot.IsCompletePivot (D z) 0 0 := by
  intro i j
  rw [D_zero_zero, abs_of_nonneg (le_of_lt hk)]
  exact hz.d_bound i j

/-! ## Step 4 on the `2 × 2` tail -/

/-- **Item 2 (step 4 legality).**  With `r > 0`, `0 ≤ s ≤ r` and `0 ≤ t ≤ r`, the
corner `(0, 0)` of `[[r, s], [t, -r]]` is a complete pivot: all four entries are
bounded by `|r| = r`. -/
theorem isCompletePivot_tail2_zero_zero (z : Point) (hz : Physical z)
    (hs : 0 ≤ z 2) (hsr : z 2 ≤ z 1) (ht : 0 ≤ z 3) :
    Rho5.Pivot.IsCompletePivot (tail2 z) 0 0 := by
  have hr : 0 < z 1 := hz.r_pos
  intro i j
  rw [tail2_zero_zero, abs_of_pos hr]
  fin_cases i <;> fin_cases j <;>
    simp [tail2, abs_of_pos hr, abs_of_nonneg hs, abs_of_nonneg ht] <;>
    first
      | exact le_rfl
      | exact hsr
      | exact hz.order_t

/-! ## Step 5 on the `1 × 1` tail -/

/-- **Item 2 (step 5 legality).**  On a `1 × 1` matrix every position is a complete
pivot. -/
theorem isCompletePivot_tail1_zero_zero (z : Point) :
    Rho5.Pivot.IsCompletePivot (tail1 z) 0 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  exact le_rfl

/-- **Item 2 (step 5, non-vanishing).**  The last pivot entry is `-z 23` with
`z 23 > 0`, hence non-zero. -/
theorem tail1_ne_zero (z : Point) (hz : Physical z) (hs : 0 ≤ z 2) (ht : 0 ≤ z 3) :
    tail1 z 0 0 ≠ 0 := by
  intro h
  have hF : 0 < z 23 := F_pos z hz hs ht
  rw [tail1_zero_zero_height z hz] at h
  linarith

end Rho5.Certificate.B24Trace
