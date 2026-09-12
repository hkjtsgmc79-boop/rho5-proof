/-
D10 / N03b — moving an arbitrary pivot to the active corner `(0, 0)`
====================================================================

`movePivot A p q` is the reindexing of `A` by `Equiv.swap 0 p` on the rows and
`Equiv.swap 0 q` on the columns.  It is the *only* pivot-moving operation of this
lane: no new pivot predicate, no new norm.

Delivered here:

* `movePivot_apply_zero_zero` — the `(0, 0)` entry of the moved matrix is exactly
  the old pivot `A p q`;
* `isCompletePivot_movePivot_iff` — `(0, 0)` is a complete pivot of the moved
  matrix exactly when `(p, q)` was one of `A`;
* the qualification facts used by every later stage: if `(p, q)` is a complete
  pivot and `A p q = 0` then `A` is the zero matrix (reusing
  `Rho5.Pivot.zero_complete_pivot`), hence for a nonzero matrix a legal pivot
  cannot vanish.

Nothing here assumes uniqueness of the maximizer, a sign convention, or a unique
pivot index; ties are handled by the frozen tied-pivot lemma.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixNormalization
import Rho5.Shared.PivotReindex.Reindex

namespace Rho5.PivotReindex

open Rho5

/-! ## Definition -/

/-- **Item 2 (definition).** Move the position `(p, q)` to the active corner
`(0, 0)` by swapping row `0` with row `p` and column `0` with column `q`.

This is `reindexEntries` with the two transpositions, so all reindexing laws
apply verbatim. -/
def movePivot {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p q : Fin (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  reindexEntries A (Equiv.swap 0 p) (Equiv.swap 0 q)

/-- Defining equation, kept for rewriting. -/
theorem movePivot_apply {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) (i j : Fin (n + 1)) :
    movePivot A p q i j = A (Equiv.swap 0 p i) (Equiv.swap 0 q j) := rfl

/-! ## The pivot really lands at `(0, 0)` -/

/-- **Item 2 (pivot position).** The `(0, 0)` entry of the moved matrix is the old
pivot `A p q`. -/
theorem movePivot_zero_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) :
    movePivot A p q 0 0 = A p q := by
  simp only [movePivot_apply, Equiv.swap_apply_left]

/-- **Item 2 (pivot predicate).** The active corner of the moved matrix is a
complete pivot exactly when `(p, q)` was a complete pivot of `A`.  The predicate is
the frozen `Rho5.Pivot.IsCompletePivot`; ties are transported, not broken. -/
theorem isCompletePivot_movePivot_iff {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) :
    Rho5.Pivot.IsCompletePivot (movePivot A p q) 0 0 ↔ Rho5.Pivot.IsCompletePivot A p q := by
  rw [movePivot, isCompletePivot_reindexEntries_iff, Equiv.swap_apply_left, Equiv.swap_apply_left]

/-- A tied maximizer of `A` becomes a complete pivot of the moved matrix at its
own moved position. -/
theorem isCompletePivot_movePivot_tied {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p p' : Fin (n + 1)) (q q' : Fin (n + 1))
    (hmax : Rho5.Pivot.IsCompletePivot A p q) (htie : |A p' q'| = |A p q|) :
    Rho5.Pivot.IsCompletePivot (movePivot A p q)
      ((Equiv.swap 0 p) p') ((Equiv.swap 0 q) q') :=
  isCompletePivot_reindexEntries_tied A (Equiv.swap 0 p) (Equiv.swap 0 q) p p' q q' hmax htie

/-! ## The qualification facts for continuing a path -/

/-- **Item 2 (vanishing pivot).** If `(p, q)` is a complete pivot of `A` and the
pivot entry `A p q` vanishes, then `A` is the zero matrix.  This is the frozen
`Rho5.Pivot.zero_complete_pivot` read on the original indices — the moved matrix
plays no role, so the statement is about `A` itself. -/
theorem eq_zero_of_isCompletePivot_of_pivot_eq_zero {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p q : Fin (n + 1))
    (hmax : Rho5.Pivot.IsCompletePivot A p q) (hzero : A p q = 0) : A = 0 := by
  funext i j
  exact Rho5.Pivot.zero_complete_pivot A p q hmax hzero i j

/-- **Item 2 (nonzero pivot).** A nonzero matrix has no vanishing complete pivot:
if `A ≠ 0` and `(p, q)` is a complete pivot then `A p q ≠ 0`.  This is the
contrapositive of the previous theorem, i.e. it uses only the proved
maximality argument — no new assumption, no `accepted` marker. -/
theorem pivot_ne_zero_of_ne_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A ≠ 0) (p q : Fin (n + 1)) (hmax : Rho5.Pivot.IsCompletePivot A p q) :
    A p q ≠ 0 :=
  fun hzero => hA (eq_zero_of_isCompletePivot_of_pivot_eq_zero A p q hmax hzero)

/-- The same qualification read at the active corner of the moved matrix: if the
moved matrix is nonzero then its `(0, 0)` entry does not vanish.  This is the form
in which the next stage (Schur elimination) consumes the hypothesis. -/
theorem movePivot_zero_zero_ne_zero_of_ne_zero {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p q : Fin (n + 1)) (hA : A ≠ 0)
    (hmax : Rho5.Pivot.IsCompletePivot A p q) :
    movePivot A p q 0 0 ≠ 0 := by
  rw [movePivot_zero_zero]
  exact pivot_ne_zero_of_ne_zero A hA p q hmax

/-- The vanishing criterion is an equivalence at the active corner: for a
complete pivot `(p, q)`, the pivot entry vanishes exactly when the whole matrix
does. -/
theorem pivot_eq_zero_iff_eq_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) (hmax : Rho5.Pivot.IsCompletePivot A p q) :
    A p q = 0 ↔ A = 0 :=
  ⟨eq_zero_of_isCompletePivot_of_pivot_eq_zero A p q hmax,
   fun h => by rw [h]; rfl⟩

/-! ## Permutation and scaling laws of `movePivot` -/

/-- `movePivot` is additive. -/
theorem movePivot_add {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) :
    movePivot (A + B) p q = movePivot A p q + movePivot B p q :=
  reindexEntries_add A B _ _

/-- The zero matrix is fixed by `movePivot`. -/
theorem movePivot_zero {n : ℕ} (p q : Fin (n + 1)) :
    movePivot (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) p q = 0 :=
  reindexEntries_zero _ _

/-- **Item 4 (preparation).** `movePivot` commutes with scalar multiplication.
This is the permutation half of the one-step scaling law; the analytic half is
D08's `Rho5.MatrixNormalization.fixedSchur_smul`. -/
theorem movePivot_smul {n : ℕ} (c : ℝ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) :
    movePivot (c • A) p q = c • movePivot A p q :=
  reindexEntries_smul c A _ _

/-- `movePivot` is injective. -/
theorem movePivot_injective {n : ℕ} (p q : Fin (n + 1)) :
    Function.Injective
      (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => movePivot A p q) :=
  reindexEntries_injective _ _

/-- Undoing the move: swapping the same rows and columns back returns `A`. -/
theorem movePivot_movePivot {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) :
    movePivot (movePivot A p q) p q = A := by
  simp only [movePivot]
  exact reindexEntries_reindex_symm A _ _

/-- Moving the pivot `(0, 0)` is the identity: the transposition `swap 0 0` is the
identity permutation.  This is the law that makes the general `pivotSchur` agree
with the frozen fixed-position `Rho5.Pivot.fixedSchur` at the active corner. -/
theorem movePivot_zero_zero_eq {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    movePivot A 0 0 = A := by
  funext i j
  simp only [movePivot_apply, Equiv.swap_self, Equiv.refl_apply]

/-- `movePivot A p q = 0` exactly when `A = 0`. -/
theorem movePivot_eq_zero_iff {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) :
    movePivot A p q = 0 ↔ A = 0 := by
  constructor
  · intro h
    have h' : movePivot A p q = movePivot 0 p q := by rw [h, movePivot_zero]
    exact movePivot_injective p q h'
  · intro h
    rw [h, movePivot_zero]

/-! ## `Matrix5` specialization of the qualification facts -/

/-- **Item 5 (continuation precondition).** For the 5 × 5 matrix of the pilot, a
complete pivot that vanishes forces the zero matrix; consequently a nonzero
`Matrix5` has a nonzero pivot at every complete-pivot position.  A recursive
five-stage path may therefore continue from any complete pivot of a nonzero
matrix, and this is derived, not assumed. -/
theorem matrix5_pivot_eq_zero_iff_eq_zero (A : Matrix5) (p q : Fin 5)
    (hmax : Rho5.Pivot.IsCompletePivot A p q) : A p q = 0 ↔ A = 0 :=
  pivot_eq_zero_iff_eq_zero A p q hmax

/-- The nonzero-pivot form for `Matrix5`. -/
theorem matrix5_pivot_ne_zero_of_ne_zero (A : Matrix5) (hA : A ≠ 0) (p q : Fin 5)
    (hmax : Rho5.Pivot.IsCompletePivot A p q) : A p q ≠ 0 :=
  pivot_ne_zero_of_ne_zero A hA p q hmax

end Rho5.PivotReindex
