/-
D20 — the complete legal trace is invariant under row/column permutation
========================================================================

**Item 3 (fixed lemma name `legalTrace_permute_iff`).** For every `n`, matrix `A`,
permutations `r`, `c` and list `values`:

  `LegalTrace (permuteEntries A r c) values ↔ LegalTrace A values`

The list `values` is **unchanged**: permuting rows and columns moves the entries
around, it does not change which absolute pivot values a legal elimination records.
Consequently every tied complete pivot is covered — the equivalence quantifies over
arbitrary `r`, `c` and both directions, and the induction below handles whatever
pivot the `step` constructor carries, with no tie-break rule anywhere.

The proof is a recursion on the order (via the trace argument), assembling the
structure of D13's relation with the D10/D20 correspondence of items 1–2:

* `empty`    — order `0`; the list is `[]` on both sides;
* `zeroStop` — the permuted matrix is zero exactly when `A` is (`permuteEntries_eq_zero_iff`);
* `step`     — the pivot `(p, q)` of the permuted matrix corresponds to `(r p, c q)` in
  `A` (`isCompletePivot_permuteEntries_iff`), the value corresponds
  (`abs_permuteEntries`), and the tail corresponds through the remaining bijections
  (`pivotSchur_permuteEntries`), where the recursion is applied at order `n`.

The reverse direction is obtained from the forward one by applying it to the inverse
permutations, so the two directions cannot disagree.
-/
import Rho5.Shared.TracePermutation.Schur
import Rho5.Shared.CompletePivotPath

namespace Rho5.TracePermutation

open Rho5

/-- **Item 3 (forward direction, generalised).** If `B` is a permutation of `A` and
`values` is a legal trace of `B`, then `values` is a legal trace of `A`.

The matrix is passed as a variable `B` with the explicit equation `B = permuteEntries A r c`
so that the recursion is structural on the trace itself; the equation is discharged by
`rfl` at every recursive call. -/
theorem legalTrace_of_permute_aux : ∀ {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ},
    Rho5.CompletePivotPath.LegalTrace B values →
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (r c : Equiv.Perm (Fin n)),
        B = permuteEntries A r c → Rho5.CompletePivotPath.LegalTrace A values
  | _, _, _, .empty, A, r, c, _ => by
      exact (Rho5.CompletePivotPath.eq_nil_iff (A := A)).mpr rfl
  | _, _, _, .zeroStop hzero, A, r, c, hEq => by
      exact Rho5.CompletePivotPath.LegalTrace.zeroStop
        ((permuteEntries_eq_zero_iff A r c).mp (hEq.symm.trans hzero))
  | _, B, _, .step p q hmax hne htail, A, r, c, hEq => by
      rw [hEq] at hmax hne htail ⊢
      refine Rho5.CompletePivotPath.LegalTrace.step (r p) (c q) ?_ ?_ ?_
      · exact (isCompletePivot_permuteEntries_iff A r c p q).mp hmax
      · exact hne
      · rw [pivotSchur_permuteEntries A r c p q] at htail
        exact legalTrace_of_permute_aux htail _ (remainingPerm r p) (remainingPerm c q) rfl

/-- **Item 3 (forward direction).** A legal trace of the permuted matrix is a legal
trace of the original one, with the same value list. -/
theorem legalTrace_of_permute {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Equiv.Perm (Fin n)) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace (permuteEntries A r c) values) :
    Rho5.CompletePivotPath.LegalTrace A values :=
  legalTrace_of_permute_aux h A r c rfl

/-- **Item 3 (reverse direction).** A legal trace of `A` is a legal trace of its
permutation, with the same value list.  Derived from the forward direction by applying
it to the inverse permutations, so no second induction is needed and the two
directions automatically agree. -/
theorem legalTrace_permute {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Equiv.Perm (Fin n)) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) :
    Rho5.CompletePivotPath.LegalTrace (permuteEntries A r c) values := by
  have h' : Rho5.CompletePivotPath.LegalTrace
      (permuteEntries (permuteEntries A r c) r.symm c.symm) values := by
    rwa [permuteEntries_permuteEntries]
  exact legalTrace_of_permute (permuteEntries A r c) r.symm c.symm h'

/-- **Item 3 (the fixed lemma).** Row/column permutation does not change the legal
traces of a matrix: the relation is invariant, with the value list held fixed. -/
theorem legalTrace_permute_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Equiv.Perm (Fin n)) (values : List ℝ) :
    Rho5.CompletePivotPath.LegalTrace (permuteEntries A r c) values ↔
      Rho5.CompletePivotPath.LegalTrace A values :=
  ⟨legalTrace_of_permute A r c, legalTrace_permute A r c⟩

/-- Existence transfers as well (a corollary of the fixed lemma, not a replacement
for it: the lemma above identifies the value lists themselves). -/
theorem exists_legalTrace_permute_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Equiv.Perm (Fin n)) :
    (∃ values, Rho5.CompletePivotPath.LegalTrace (permuteEntries A r c) values) ↔
      ∃ values, Rho5.CompletePivotPath.LegalTrace A values :=
  ⟨fun ⟨v, hv⟩ => ⟨v, (legalTrace_permute_iff A r c v).mp hv⟩,
   fun ⟨v, hv⟩ => ⟨v, (legalTrace_permute_iff A r c v).mpr hv⟩⟩

/-- **Item 3 (tie coverage, explicit).** Any legal pivot `(p, q)` of the permuted
matrix is matched by the legal pivot `(r p, c q)` of `A` with the same absolute value;
combined with the fixed lemma this is what makes the equivalence independent of any
tie-break rule. -/
theorem isCompletePivot_permuteEntries_tied {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Equiv.Perm (Fin n)) (p q : Fin n)
    (hmax : Rho5.Pivot.IsCompletePivot (permuteEntries A r c) p q) :
    Rho5.Pivot.IsCompletePivot A (r p) (c q) ∧
      |permuteEntries A r c p q| = |A (r p) (c q)| :=
  ⟨(isCompletePivot_permuteEntries_iff A r c p q).mp hmax, abs_permuteEntries A r c p q⟩

/-- **Item 3 (two-step form).** Permuting twice composes: the relation is invariant
under the composite permutation as well. -/
theorem legalTrace_permute_permute_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r c r' c' : Equiv.Perm (Fin n)) (values : List ℝ) :
    Rho5.CompletePivotPath.LegalTrace
        (permuteEntries (permuteEntries A r c) r' c') values ↔
      Rho5.CompletePivotPath.LegalTrace A values :=
  (legalTrace_permute_iff (permuteEntries A r c) r' c' values).trans
    (legalTrace_permute_iff A r c values)

end Rho5.TracePermutation
