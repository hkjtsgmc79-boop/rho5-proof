/-
D11 — 合法完整主元的一步增长界与乘子界
=========================================

Purpose (frozen by the D11 task card): provide the local growth control and
multiplier bounds that the full elimination path will need.  This module does
**not** claim an optimal RHO5 bound, attainability, a five-stage recursion, a
global growth rate, or anything about determinants/ranks; and it does not do row
or column reindexing or arbitrary-pivot updates (owned by D10).

Reused unchanged from the frozen inputs (read-only):
* `Rho5.Pivot.IsCompletePivot`, `Rho5.Pivot.fixedSchur`,
  `Rho5.Pivot.zero_complete_pivot` (`Rho5.Shared.Pivot`);
* `Rho5.Matrix5`, `Rho5.matrixEntryMax` (`Rho5.Shared.Conventions`);
* `Rho5.MatrixNormalization.normalize`, `abs_entry_le_matrixEntryMax`,
  `matrixEntryMax_normalize`, `isCompletePivot_normalize_iff`,
  `normalize_eq_inv_smul`, `smul_apply_entry`, `matrixEntryMax_ne_zero`
  (`Rho5.Shared.MatrixNormalization`, D08).

Delivered (namespace `Rho5.PivotGrowth`):

1. row/column multiplier bounds — `row_multiplier_abs_le_one`,
   `col_multiplier_abs_le_one`, `multipliers_abs_le_one`: for a legal pivot at
   `(0,0)` with `A 0 0 ≠ 0`, every `|A i 0 / A 0 0| ≤ 1` and
   `|A 0 j / A 0 0| ≤ 1`.  Negative pivots and tied maxima are allowed; no
   positivity or uniqueness of the maximizer is assumed;
2. one-step growth — `fixedSchur_entry_abs_le_two_mul_pivot`:
   `|fixedSchur A i j| ≤ 2 * |A 0 0|` for all `i j : Fin n`, derived directly
   from the update formula and the complete-pivot property;
3. abstract propagation interface —
   `fixedSchur_entry_abs_le_two_mul_of_entry_bound`: if additionally
   `∀ i j, |A i j| ≤ B` then `|fixedSchur A i j| ≤ 2 * B`.  This extra `B`
   hypothesis is only an interface and does not replace item 2;
4. `Matrix5` specialization — `fixedSchur_entry_abs_le_two_matrixEntryMax`
   (`≤ 2 * matrixEntryMax A`), `eq_zero_of_pivot_eq_zero` (a vanishing legal
   pivot forces the whole matrix to vanish, so the mathematical elimination path
   *terminates* there; Lean's total division is not a legitimate continuation),
   `normalize_pivot_qualified` (normalization preserves legal pivot status and
   keeps the pivot nonzero), and `normalize_fixedSchur_entry_abs_le_two`
   (`≤ 2` for every entry of the normalized update, with the normalization
   qualification derived from the original one, not assumed).

No `sorry`, no new axiom; every public theorem keeps the nonzero-pivot
qualification explicit.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixNormalization
import Mathlib.Algebra.Order.Field.Basic

namespace Rho5.PivotGrowth

open Rho5

/-! ## 1. Row and column multiplier bounds -/

/-- **Item 1 (rows).** For a legal complete pivot at `(0,0)` with nonzero pivot
value, every row multiplier is bounded by `1` in absolute value.  No sign or
uniqueness assumption on the pivot is made: `IsCompletePivot` alone supplies
`|A i 0| ≤ |A 0 0|`, and `|A 0 0| > 0` is used to divide. -/
theorem row_multiplier_abs_le_one {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hmax : Rho5.Pivot.IsCompletePivot A 0 0) (hA : A 0 0 ≠ 0) (i : Fin (n + 1)) :
    |A i 0 / A 0 0| ≤ 1 := by
  rw [abs_div, div_le_iff₀ (abs_pos.mpr hA), one_mul]
  exact hmax i 0

/-- **Item 1 (columns).** Same statement for the column multipliers. -/
theorem col_multiplier_abs_le_one {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hmax : Rho5.Pivot.IsCompletePivot A 0 0) (hA : A 0 0 ≠ 0) (j : Fin (n + 1)) :
    |A 0 j / A 0 0| ≤ 1 := by
  rw [abs_div, div_le_iff₀ (abs_pos.mpr hA), one_mul]
  exact hmax 0 j

/-- **Item 1 (combined interface).** All row and column multipliers bound by `1`
simultaneously, in the form most convenient for downstream estimates. -/
theorem multipliers_abs_le_one {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hmax : Rho5.Pivot.IsCompletePivot A 0 0) (hA : A 0 0 ≠ 0) :
    (∀ i, |A i 0 / A 0 0| ≤ 1) ∧ (∀ j, |A 0 j / A 0 0| ≤ 1) :=
  ⟨fun i => row_multiplier_abs_le_one A hmax hA i,
   fun j => col_multiplier_abs_le_one A hmax hA j⟩

/-! ## 2. One-step growth bound -/

/-- **Item 2 (one-step growth).** Under a legal nonzero pivot at `(0,0)`, every
entry of the actual Schur update is bounded by twice the absolute pivot value:
`|A i+1 j+1 - A i+1 0 * A 0 j+1 / A 0 0| ≤ 2 * |A 0 0|`.  The proof uses only
the update formula and `|A i j| ≤ |A 0 0|`; the multiplier bounds and the growth
bound are conclusions here, never hypotheses. -/
theorem fixedSchur_entry_abs_le_two_mul_pivot {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hmax : Rho5.Pivot.IsCompletePivot A 0 0) (hA : A 0 0 ≠ 0) (i j : Fin n) :
    |Rho5.Pivot.fixedSchur A i j| ≤ 2 * |A 0 0| := by
  have hp : 0 < |A 0 0| := abs_pos.mpr hA
  have h1 : |A i.succ j.succ| ≤ |A 0 0| := hmax _ _
  have h2 : |A i.succ 0| ≤ |A 0 0| := hmax _ _
  have h3 : |A 0 j.succ| ≤ |A 0 0| := hmax _ _
  -- the subtracted correction term is itself bounded by the pivot value
  have hb : |A i.succ 0 * A 0 j.succ / A 0 0| ≤ |A 0 0| := by
    rw [abs_div, abs_mul, div_le_iff₀ hp]
    exact mul_le_mul h2 h3 (abs_nonneg _) (le_of_lt hp)
  rw [Rho5.Pivot.fixedSchur, abs_sub_le_iff]
  constructor
  · calc A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0
        ≤ |A 0 0| - (-(|A 0 0|)) := sub_le_sub (abs_le.mp h1).2 (abs_le.mp hb).1
      _ = 2 * |A 0 0| := by ring
  · calc A i.succ 0 * A 0 j.succ / A 0 0 - A i.succ j.succ
        ≤ |A 0 0| - (-(|A 0 0|)) := sub_le_sub (abs_le.mp hb).2 (abs_le.mp h1).1
      _ = 2 * |A 0 0| := by ring

/-! ## 3. Entry-wise bound interface -/

/-- **Item 3 (abstract propagation interface).** If every entry of the original
matrix is bounded by a common `B`, the one-step growth bound becomes `2 * B`.
The `B` hypothesis is an interface for downstream composition only: item 2 above
is proved without it. -/
theorem fixedSchur_entry_abs_le_two_mul_of_entry_bound {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (B : ℝ)
    (hmax : Rho5.Pivot.IsCompletePivot A 0 0) (hA : A 0 0 ≠ 0)
    (hB : ∀ i j, |A i j| ≤ B) (i j : Fin n) :
    |Rho5.Pivot.fixedSchur A i j| ≤ 2 * B :=
  calc |Rho5.Pivot.fixedSchur A i j| ≤ 2 * |A 0 0| :=
        fixedSchur_entry_abs_le_two_mul_pivot A hmax hA i j
    _ ≤ 2 * B := mul_le_mul_of_nonneg_left (hB 0 0) (by norm_num)

/-! ## 4. `Matrix5` specialization and normalization -/

/-- **Item 4a (`Matrix5`, entry-max form).** For the 5×5 matrix of the frozen
conventions with a legal nonzero pivot at `(0,0)`, all 4×4 updated entries are
bounded by `2 * matrixEntryMax A` (D08's entry-max bound supplies
`|A 0 0| ≤ matrixEntryMax A`). -/
theorem fixedSchur_entry_abs_le_two_matrixEntryMax (A : Matrix5)
    (hmax : Rho5.Pivot.IsCompletePivot A 0 0) (hA : A 0 0 ≠ 0) (i j : Fin 4) :
    |Rho5.Pivot.fixedSchur A i j| ≤ 2 * matrixEntryMax A :=
  calc |Rho5.Pivot.fixedSchur A i j| ≤ 2 * |A 0 0| :=
        fixedSchur_entry_abs_le_two_mul_pivot A hmax hA i j
    _ ≤ 2 * matrixEntryMax A :=
        mul_le_mul_of_nonneg_left (Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax A 0 0)
          (by norm_num)

/-- **Zero-pivot degeneracy (path termination).** If the legal complete pivot at
`(0,0)` vanishes, the whole matrix vanishes (this is D08/Pivot's
`zero_complete_pivot` in matrix form).  Consequently no legitimate elimination
step exists: Lean's total real division would still return a value, but that
value is an artifact of the encoding, not a mathematical continuation. -/
theorem eq_zero_of_pivot_eq_zero (A : Matrix5) (hmax : Rho5.Pivot.IsCompletePivot A 0 0)
    (h0 : A 0 0 = 0) : A = 0 :=
  funext fun i => funext fun j => Rho5.Pivot.zero_complete_pivot A 0 0 hmax h0 i j

/-- **Item 4b (normalization qualification).** For a nonzero `Matrix5` whose
`(0,0)` is a legal complete pivot, the normalized matrix again has a legal
complete pivot at `(0,0)`, and that normalized pivot is nonzero.  Both facts are
derived from the original qualification (plus D08's normalization theorems); the
pivot value `A 0 0 ≠ 0` is recovered from `A ≠ 0` via
`eq_zero_of_pivot_eq_zero`. -/
theorem normalize_pivot_qualified (A : Matrix5) (hM : A ≠ 0)
    (hmax : Rho5.Pivot.IsCompletePivot A 0 0) :
    Rho5.Pivot.IsCompletePivot (Rho5.MatrixNormalization.normalize A) 0 0 ∧
      Rho5.MatrixNormalization.normalize A 0 0 ≠ 0 := by
  have hA00 : A 0 0 ≠ 0 := by
    intro h0
    exact hM (eq_zero_of_pivot_eq_zero A hmax h0)
  refine ⟨(Rho5.MatrixNormalization.isCompletePivot_normalize_iff A hM 0 0).mpr hmax, ?_⟩
  rw [Rho5.MatrixNormalization.normalize_eq_inv_smul, Rho5.MatrixNormalization.smul_apply_entry]
  exact mul_ne_zero (inv_ne_zero (Rho5.MatrixNormalization.matrixEntryMax_ne_zero A hM)) hA00

/-- **Item 4b (normalized update bound).** For a nonzero `Matrix5` with a legal
`(0,0)` pivot, every entry of the 4×4 update of the *normalized* matrix is
bounded by `2` (because the normalized entry maximum is `1`).  The normalization
qualification is derived, not assumed. -/
theorem normalize_fixedSchur_entry_abs_le_two (A : Matrix5) (hM : A ≠ 0)
    (hmax : Rho5.Pivot.IsCompletePivot A 0 0) (i j : Fin 4) :
    |Rho5.Pivot.fixedSchur (Rho5.MatrixNormalization.normalize A) i j| ≤ 2 := by
  obtain ⟨hmaxN, hN00⟩ := normalize_pivot_qualified A hM hmax
  calc |Rho5.Pivot.fixedSchur (Rho5.MatrixNormalization.normalize A) i j|
      ≤ 2 * matrixEntryMax (Rho5.MatrixNormalization.normalize A) :=
        fixedSchur_entry_abs_le_two_matrixEntryMax (Rho5.MatrixNormalization.normalize A)
          hmaxN hN00 i j
    _ = 2 := by rw [Rho5.MatrixNormalization.matrixEntryMax_normalize A hM]; norm_num

end Rho5.PivotGrowth
