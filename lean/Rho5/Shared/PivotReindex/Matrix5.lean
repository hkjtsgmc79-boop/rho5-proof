/-
D10 / N03b — the `Matrix5` (n = 4) instance and the continuation precondition
=============================================================================

This file is the direct-use layer for the pilot's 5 × 5 matrix:

* `Matrix4` and `pivotSchur4` — the alias by which `Matrix5` produces the 4 × 4
  matrix of the next stage (no new mathematics, just the `n = 4` instance);
* worked evaluations showing that the moved pivot really lands at `(0, 0)` and that
  the Schur entry at `(0, 0)` is written in the original indices;
* the precondition a recursive continuation must carry, as a *derived* statement:
  a complete pivot of a nonzero matrix is nonzero, and a vanishing complete pivot
  forces the zero matrix.

Scope note (frozen): this lane stops here.  It does not build the five-stage
recursive path, does not bound the global growth, and does not claim
attainability; it supplies the permutation / arbitrary-pivot / one-step-elimination
layer those later stages consume.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixNormalization
import Rho5.Shared.PivotReindex.Reindex
import Rho5.Shared.PivotReindex.MovePivot
import Rho5.Shared.PivotReindex.Remaining
import Rho5.Shared.PivotReindex.Schur

namespace Rho5.PivotReindex

open Rho5

/-! ## The 5 × 5 → 4 × 4 instance -/

/-- The 4 × 4 real matrix produced by one pivot step on a `Matrix5`. -/
abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℝ

/-- **Item 5 (direct-use alias).** One Schur step on the pilot's `Matrix5` with the
pivot `(p, q)` moved to the active corner.  This is the `n = 4` instance of
`pivotSchur`; nothing new is defined. -/
noncomputable def pivotSchur4 (A : Matrix5) (p q : Fin 5) : Matrix4 :=
  pivotSchur A p q

/-- The alias unfolds to the general one-step update. -/
theorem pivotSchur4_eq_pivotSchur (A : Matrix5) (p q : Fin 5) :
    pivotSchur4 A p q = pivotSchur A p q := rfl

/-- **Item 5 (formula at `Matrix5`).** The 4 × 4 entries of one pivot step written
in the original row/column indices of `A`. -/
theorem pivotSchur4_apply (A : Matrix5) (p q : Fin 5) (i j : Fin 4) :
    pivotSchur4 A p q i j =
      A (remainingIndex p i) (remainingIndex q j)
        - A (remainingIndex p i) q * A p (remainingIndex q j) / A p q :=
  pivotSchur_apply A p q i j

/-- The pivot of a `Matrix5` lands at `(0, 0)` of the moved matrix. -/
theorem matrix5_movePivot_zero_zero (A : Matrix5) (p q : Fin 5) :
    movePivot A p q 0 0 = A p q :=
  movePivot_zero_zero A p q

/-- The complete-pivot property of a `Matrix5` transports to the active corner. -/
theorem matrix5_isCompletePivot_movePivot_iff (A : Matrix5) (p q : Fin 5) :
    Rho5.Pivot.IsCompletePivot (movePivot A p q) 0 0 ↔ Rho5.Pivot.IsCompletePivot A p q :=
  isCompletePivot_movePivot_iff A p q

/-- The one-step scaling law at `Matrix5`, with the pivot qualification *derived*
from `A ≠ 0` plus the complete-pivot property. -/
theorem pivotSchur4_smul_of_isCompletePivot (A : Matrix5) (p q : Fin 5) {c : ℝ}
    (hc : c ≠ 0) (hA : A ≠ 0) (hmax : Rho5.Pivot.IsCompletePivot A p q) :
    pivotSchur4 (c • A) p q = c • pivotSchur4 A p q :=
  pivotSchur_smul_of_isCompletePivot A p q hc hA hmax

/-- The one-step scaling law at `Matrix5` with both hypotheses explicit. -/
theorem pivotSchur4_smul (A : Matrix5) (p q : Fin 5) {c : ℝ} (hc : c ≠ 0)
    (hA : A p q ≠ 0) :
    pivotSchur4 (c • A) p q = c • pivotSchur4 A p q :=
  pivotSchur_smul A p q hc hA

/-! ## Computable remaining indices (no permutation enumeration) -/

/-- The remaining-index map is decidable, so concrete index bookkeeping for the
5 × 5 instance is checked by evaluation rather than by case enumeration.  Example:
after moving the pivot `3` to `0`, the remaining index `0` is the original row `1`. -/
theorem remainingIndex_fin5_example : remainingIndex (3 : Fin 5) (0 : Fin 4) = 1 := by decide

/-- A second evaluation, for the column side: moving the pivot `2` to `0` leaves
column `1` in position `0`. -/
theorem remainingIndex_fin5_example' : remainingIndex (2 : Fin 5) (0 : Fin 4) = 1 := by decide

/-- Every remaining index of the `Matrix5` instance, evaluated: with the pivot `p`
moved to `0`, the four non-pivot indices are hit in the order `remainingIndex p ·`. -/
theorem remainingIndex_fin5_zero : remainingIndex (0 : Fin 5) (0 : Fin 4) = 1 := by decide

/-- The pivot index is never among the remaining indices (the `Matrix5` instance). -/
theorem remainingIndex_fin5_ne (p : Fin 5) (i : Fin 4) : remainingIndex p i ≠ p :=
  remainingIndex_ne p i

/-! ## Worked example: the moved pivot and the first Schur entry -/

/-- **Worked example (direct use).** For a `Matrix5` and the pivot position
`(3, 2)`, the moved matrix has `A 3 2` at the active corner, and the `(0, 0)` entry
of the 4 × 4 update is the Schur entry at the original indices `(1, 1)`. -/
theorem matrix5_worked_example (A : Matrix5) :
    movePivot A 3 2 0 0 = A 3 2 ∧
      pivotSchur4 A 3 2 0 0 = A 1 1 - A 1 2 * A 3 1 / A 3 2 := by
  refine ⟨movePivot_zero_zero A 3 2, ?_⟩
  rw [pivotSchur4_apply]
  simp only [remainingIndex_fin5_example, remainingIndex_fin5_example']

/-! ## The continuation precondition (derived, not assumed) -/

/-- **Item 5 (precondition).** The two facts a recursive continuation needs at a
chosen pivot: the position is a complete pivot, and the pivot entry is nonzero.
Both are *derived* facts about `A`; neither is an extra axiom, and the structure
does not weaken the frozen `Rho5.Pivot.IsCompletePivot`. -/
structure PivotReady (A : Matrix5) (p q : Fin 5) : Prop where
  isPivot : Rho5.Pivot.IsCompletePivot A p q
  pivot_ne_zero : A p q ≠ 0

/-- A complete pivot of a nonzero matrix is ready to continue.  The nonzero-pivot
fact is derived from the frozen `zero_complete_pivot`, so no sign, uniqueness or
tie-breaking hypothesis enters. -/
theorem pivotReady_of_ne_zero {A : Matrix5} (hA : A ≠ 0) {p q : Fin 5}
    (hmax : Rho5.Pivot.IsCompletePivot A p q) : PivotReady A p q :=
  ⟨hmax, matrix5_pivot_ne_zero_of_ne_zero A hA p q hmax⟩

/-- **Item 5 (exact precondition).** For a complete pivot, readiness is exactly
"the matrix is nonzero": the only way to fail to continue is the zero matrix. -/
theorem pivotReady_iff {A : Matrix5} {p q : Fin 5}
    (hmax : Rho5.Pivot.IsCompletePivot A p q) :
    PivotReady A p q ↔ A ≠ 0 := by
  constructor
  · rintro ⟨-, hne⟩ hzero
    exact hne (by rw [hzero]; rfl)
  · exact fun hA => pivotReady_of_ne_zero hA hmax

/-- The zero matrix has no ready pivot: every complete pivot of `0` has pivot
entry `0`.  This is the case in which the recursive path stops. -/
theorem not_pivotReady_zero (p q : Fin 5) : ¬ PivotReady (0 : Matrix5) p q := by
  rintro ⟨-, hne⟩
  exact hne rfl

/-- Readiness exposes the complete-pivot property. -/
theorem PivotReady.isCompletePivot {A : Matrix5} {p q : Fin 5} (h : PivotReady A p q) :
    Rho5.Pivot.IsCompletePivot A p q :=
  h.isPivot

/-- Readiness exposes the nonzero pivot, i.e. the qualification the *next* Schur
step needs; the two steps compose without re-deriving anything. -/
theorem PivotReady.pivot_ne_zero' {A : Matrix5} {p q : Fin 5} (h : PivotReady A p q) :
    A p q ≠ 0 :=
  h.pivot_ne_zero

/-- Composition: a ready pivot of a nonzero `Matrix5` makes the next one-step
scaling law available at the same position. -/
theorem pivotSchur4_smul_of_pivotReady {A : Matrix5} {p q : Fin 5} (h : PivotReady A p q)
    {c : ℝ} (hc : c ≠ 0) :
    pivotSchur4 (c • A) p q = c • pivotSchur4 A p q :=
  pivotSchur4_smul A p q hc h.pivot_ne_zero

end Rho5.PivotReindex
