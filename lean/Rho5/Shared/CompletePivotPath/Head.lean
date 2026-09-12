/-
D13 — the head of a trace is the largest entry
==============================================

**Goal 2.** For a positive-order matrix, the first recorded value of any legal trace
is exactly the maximum absolute entry of that matrix, and that maximum is attained.
Both directions are derived from the *actual* relation:

* every entry is bounded by the head, because the head comes from a complete pivot
  (`Rho5.Pivot.IsCompletePivot` is the frozen predicate, transported unchanged);
* the head is attained, because it *is* the absolute value of an actual entry;
* at a positive-order zero matrix the head is `0` and the matrix is zero, which is
  the same statement.

Consequently, a caller never has to supply "`v` is the maximum" as an extra
hypothesis, and the statement does not depend on the (separately developed)
stagewise entry maximum of D12.
-/
import Rho5.Shared.CompletePivotPath.Basic
import Rho5.Shared.MatrixNormalization

namespace Rho5.CompletePivotPath

open Rho5

/-- **Goal 2 (head is the max).** If `v :: vs` is a legal trace of the positive-order
matrix `A`, then every entry of `A` is bounded by `v` and some entry attains `v`. -/
theorem head_isMax {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {v : ℝ}
    {vs : List ℝ} (h : LegalTrace A (v :: vs)) :
    (∀ i j, |A i j| ≤ v) ∧ ∃ p q : Fin (n + 1), |A p q| = v := by
  cases h with
  | zeroStop hzero =>
      refine ⟨?_, 0, 0, ?_⟩
      · intro i j
        rw [hzero]
        simp
      · rw [hzero]
        simp
  | step p q hmax hne htail => exact ⟨hmax, p, q, rfl⟩

/-- The bound half of goal 2, as a standalone statement. -/
theorem le_head {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {v : ℝ}
    {vs : List ℝ} (h : LegalTrace A (v :: vs)) (i j : Fin (n + 1)) : |A i j| ≤ v :=
  (head_isMax h).1 i j

/-- The attainment half of goal 2, as a standalone statement. -/
theorem exists_abs_eq_head {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {v : ℝ}
    {vs : List ℝ} (h : LegalTrace A (v :: vs)) : ∃ p q : Fin (n + 1), |A p q| = v :=
  (head_isMax h).2

/-- **Goal 4 (head of a `Matrix5` trace).** For a nonzero `5 × 5` matrix the head of
any legal trace is exactly the frozen entry maximum `Rho5.matrixEntryMax`.  The
`A ≠ 0` hypothesis is what excludes the `zeroStop` branch, where the head is `0`
while the entry maximum of a nonzero matrix is positive. -/
theorem head_eq_matrixEntryMax {A : Matrix5} (hA : A ≠ 0) {v : ℝ} {vs : List ℝ}
    (h : LegalTrace A (v :: vs)) : v = matrixEntryMax A := by
  obtain ⟨hmax, p, q, hpq⟩ := head_isMax h
  have h1 : matrixEntryMax A ≤ |A p q| := by
    unfold matrixEntryMax
    exact Finset.sup'_le Finset.univ_nonempty _
      (fun ij _ => by rw [hpq]; exact hmax ij.1 ij.2)
  have h2 : |A p q| ≤ matrixEntryMax A :=
    Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax A p q
  rw [← hpq]
  exact le_antisymm h2 h1

/-- The attainment form of the previous statement: for a nonzero `Matrix5`, some
entry attains the frozen entry maximum, and it is exactly the head of the trace. -/
theorem exists_abs_eq_matrixEntryMax {A : Matrix5} (hA : A ≠ 0) {v : ℝ} {vs : List ℝ}
    (h : LegalTrace A (v :: vs)) : ∃ p q : Fin 5, |A p q| = matrixEntryMax A := by
  obtain ⟨p, q, hpq⟩ := exists_abs_eq_head h
  exact ⟨p, q, by rw [hpq, head_eq_matrixEntryMax hA h]⟩

end Rho5.CompletePivotPath
