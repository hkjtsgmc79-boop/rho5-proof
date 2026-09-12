/-
D10 / N03b — one Schur elimination step at an arbitrary pivot position
======================================================================

`pivotSchur A p q` is the Schur update of `A` after the pivot `(p, q)` has been
moved to the active corner: it is the frozen `Rho5.Pivot.fixedSchur` applied to
`movePivot A p q` — no second Schur definition.

Delivered here:

* the **true entrywise formula** at the original indices, valid for arbitrary
  `p`, `q`:
  `pivotSchur A p q i j = A (remainingIndex p i) (remainingIndex q j)
      - A (remainingIndex p i) q * A p (remainingIndex q j) / A p q`;
* consistency with the frozen fixed-position update
  (`pivotSchur (movePivot A p q) 0 0 = fixedSchur (movePivot A p q)`);
* the **one-step scaling law** `pivotSchur (c • A) p q = c • pivotSchur A p q`,
  obtained from `movePivot_smul` and D08's `fixedSchur_smul`, carrying the two
  explicit hypotheses `c ≠ 0` and `A p q ≠ 0`.

The definition is total (real division is total), but every theorem that
*interprets* it as a legitimate elimination step carries `A p q ≠ 0` explicitly.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixNormalization
import Rho5.Shared.PivotReindex.MovePivot
import Rho5.Shared.PivotReindex.Remaining

namespace Rho5.PivotReindex

open Rho5

/-! ## Definition -/

/-- **Item 4 (definition).** One Schur elimination step with the pivot `(p, q)`
moved to `(0, 0)`.  Total as a real expression; the qualification `A p q ≠ 0`
that makes it the Schur complement of a legal step is an explicit hypothesis of
every theorem below that uses it as such. -/
noncomputable def pivotSchur {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) : Matrix (Fin n) (Fin n) ℝ :=
  Rho5.Pivot.fixedSchur (movePivot A p q)

/-- Defining equation, kept for rewriting. -/
theorem pivotSchur_eq_fixedSchur {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) :
    pivotSchur A p q = Rho5.Pivot.fixedSchur (movePivot A p q) := rfl

/-! ## The entrywise formula at the original indices -/

/-- **Item 4 (formula).** The Schur update written back in the *original* row and
column indices `remainingIndex p ·` and `remainingIndex q ·`, with the pivot entry
`A p q` in the denominator.  The remaining-index bookkeeping of item 3 is what
makes this an honest enumeration of the non-pivot rows and columns. -/
theorem pivotSchur_apply {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) (i j : Fin n) :
    pivotSchur A p q i j =
      A (remainingIndex p i) (remainingIndex q j)
        - A (remainingIndex p i) q * A p (remainingIndex q j) / A p q := by
  simp only [pivotSchur, Rho5.Pivot.fixedSchur, movePivot_apply, remainingIndex_apply,
    Equiv.swap_apply_left]

/-- The formula in the "moved" orientation, i.e. the frozen fixed-position update
of the moved matrix, for comparison with `Rho5.Pivot.fixedSchur`. -/
theorem pivotSchur_apply_movePivot {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) (i j : Fin n) :
    pivotSchur A p q i j =
      movePivot A p q i.succ j.succ
        - movePivot A p q i.succ 0 * movePivot A p q 0 j.succ / movePivot A p q 0 0 :=
  rfl

/-- **Consistency with the frozen fixed-position update.** Applying the general
`pivotSchur` to the already-moved matrix at the pivot position `(0, 0)` reproduces
the frozen `Rho5.Pivot.fixedSchur` of the moved matrix: moving the pivot `0` to
`0` is the identity permutation. -/
theorem pivotSchur_movePivot_zero_zero {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p q : Fin (n + 1)) :
    pivotSchur (movePivot A p q) 0 0 = Rho5.Pivot.fixedSchur (movePivot A p q) := by
  rw [pivotSchur, movePivot_zero_zero_eq]

/-- The `(i, j)` entry of the update in the moved orientation, exposing the pivot
`A p q` in the denominator through `movePivot_zero_zero`. -/
theorem pivotSchur_apply_denom {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) (i j : Fin n) :
    pivotSchur A p q i j =
      A (remainingIndex p i) (remainingIndex q j)
        - A (remainingIndex p i) q * A p (remainingIndex q j) / A p q :=
  pivotSchur_apply A p q i j

/-! ## One-step scaling law -/

/-- **Item 4 (scaling).** Scaling the matrix by a nonzero scalar scales the
one-step Schur update with the *same* pivot by the same scalar, provided the pivot
entry `A p q` is nonzero.  Proof: `movePivot_smul` (permutation half) followed by
D08's `Rho5.MatrixNormalization.fixedSchur_smul` (analytic half).  Both
qualifications are explicit: `hc : c ≠ 0` and `hA : A p q ≠ 0`. -/
theorem pivotSchur_smul {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) {c : ℝ} (hc : c ≠ 0) (hA : A p q ≠ 0) :
    pivotSchur (c • A) p q = c • pivotSchur A p q := by
  have h00 : movePivot A p q 0 0 ≠ 0 := by
    rwa [movePivot_zero_zero]
  rw [pivotSchur, movePivot_smul,
    Rho5.MatrixNormalization.fixedSchur_smul (movePivot A p q) hc h00, pivotSchur]

/-- Pointwise form of the one-step scaling law. -/
theorem pivotSchur_smul_apply {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) {c : ℝ} (hc : c ≠ 0) (hA : A p q ≠ 0) (i j : Fin n) :
    pivotSchur (c • A) p q i j = c * pivotSchur A p q i j := by
  rw [pivotSchur_smul A p q hc hA, Rho5.MatrixNormalization.smul_apply_entry]

/-- The scaling law with the hypotheses read off a complete pivot of a nonzero
matrix: the qualification `A p q ≠ 0` is *derived* from `A ≠ 0` and the pivot
property, not assumed separately. -/
theorem pivotSchur_smul_of_isCompletePivot {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p q : Fin (n + 1)) {c : ℝ}
    (hc : c ≠ 0) (hA : A ≠ 0) (hmax : Rho5.Pivot.IsCompletePivot A p q) :
    pivotSchur (c • A) p q = c • pivotSchur A p q :=
  pivotSchur_smul A p q hc (pivot_ne_zero_of_ne_zero A hA p q hmax)

/-- The same, pointwise, with the pivot qualification derived. -/
theorem pivotSchur_smul_apply_of_isCompletePivot {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p q : Fin (n + 1)) {c : ℝ}
    (hc : c ≠ 0) (hA : A ≠ 0) (hmax : Rho5.Pivot.IsCompletePivot A p q) (i j : Fin n) :
    pivotSchur (c • A) p q i j = c * pivotSchur A p q i j :=
  pivotSchur_smul_apply A p q hc (pivot_ne_zero_of_ne_zero A hA p q hmax) i j

/-! ## Basic laws -/

/-- The update of the zero matrix is the zero matrix. -/
theorem pivotSchur_zero {n : ℕ} (p q : Fin (n + 1)) :
    pivotSchur (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) p q = 0 := by
  funext i j
  simp only [pivotSchur_apply, Matrix.zero_apply]
  ring

/-- **Sanity check at `n = 1` (a 2 × 2 matrix).** With the pivot in the active
corner `(0, 0)` the update is the classical Schur complement
`A 1 1 - A 1 0 * A 0 1 / A 0 0`, and with the pivot at the *other* corner `(1, 1)`
it is the Schur complement read at that corner, `A 0 0 - A 0 1 * A 1 0 / A 1 1`.
This is the smallest direct-use instance of the general formula: the pivot entry in
the denominator is the moved one, exactly as `pivotSchur_apply` prescribes.

Honesty note: the update is **not** additive in the matrix — `A` and `B` share only
the pivot *position*, not the denominator `A p q + B p q` — so no additivity law is
stated. -/
theorem pivotSchur_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    pivotSchur A 0 0 0 0 = A 1 1 - A 1 0 * A 0 1 / A 0 0 ∧
      pivotSchur A 1 1 0 0 = A 0 0 - A 0 1 * A 1 0 / A 1 1 := by
  have h0 : remainingIndex (0 : Fin 2) (0 : Fin 1) = 1 := by decide
  have h1 : remainingIndex (1 : Fin 2) (0 : Fin 1) = 0 := by decide
  constructor <;> rw [pivotSchur_apply] <;> simp only [h0, h1]

end Rho5.PivotReindex
