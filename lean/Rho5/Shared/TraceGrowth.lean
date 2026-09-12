/-
D15 — 任意合法消元轨迹的逐阶段粗增长界
=========================================

Purpose (frozen by the D15 card): the coarse, provable growth bound shared by
*every* legal complete-pivot elimination trace.  It serves the boundedness of the
growth-value set; it is **not** the final optimal `alpha` bound, it does not claim
`16 = RHO5`, optimality or attainability, and it neither proves path existence
(D14) nor defines the growth ratio / value set (D17).

Reused unchanged (read-only):
* `Rho5.PivotReindex.{movePivot, pivotSchur, isCompletePivot_movePivot_iff, …}` (D10);
* `Rho5.PivotGrowth.fixedSchur_entry_abs_le_two_mul_pivot`,
  `…_of_entry_bound` (D11);
* `Rho5.MatrixStage.{stageEntryMax, abs_entry_le_stageEntryMax,
  stageEntryMax_nonneg}` (D12);
* `Rho5.CompletePivotPath.{LegalTrace, length_le}` (D13);
* `Rho5.MatrixNormalization.{abs_entry_le_matrixEntryMax, matrixEntryMax_nonneg,
  matrixEntryMax_normalize}` (D08).

Delivered (namespace `Rho5.TraceGrowth`):

1. `pivotSchur_entry_abs_le_two_mul_pivot` /
   `pivotSchur_entry_abs_le_two_mul_of_entry_bound` — D11's fixed-corner one-step
   growth bound transported to an arbitrary legal nonzero pivot `(p, q)` through
   D10's `movePivot` (reusing the actual `pivotSchur` formula, not a new
   multiplication classification);
2. `ListBoundBy`, `listBoundBy_cons`, `legalTrace_boundBy` — the stagewise
   `2^k` propagation: along any legal trace, the `k`-th recorded pivot value is at
   most `2^k * B` whenever every original entry is bounded by `B`.  The zero-matrix
   early stop is covered by its own constructor case; no full-rank, every-step-
   nonzero or unique-pivot assumption is used, and no step silently re-normalizes;
3. `trace_get_le_pow_mul_stageEntryMax`, `trace_value_le_pow_mul_stageEntryMax`
   (every trace value of an `(n+1) × (n+1)` matrix is `≤ 2^n * stageEntryMax A`)
   and the `Matrix5` statements `trace_get_le_sixteen`, `trace_value_le_sixteen`
   (`≤ 16 * matrixEntryMax A`) and `normalize_trace_value_le_sixteen`
   (`≤ 16` for the normalization of a nonzero `Matrix5`).

No `sorry`, no new axiom.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixNormalization
import Rho5.Shared.PivotReindex
import Rho5.Shared.PivotGrowth
import Rho5.Shared.MatrixStage
import Rho5.Shared.CompletePivotPath
import Mathlib.Algebra.Order.Field.Basic

namespace Rho5.TraceGrowth

open Rho5

/-! ## 1. One-step growth at an arbitrary legal pivot (via D10 `movePivot`) -/

/-- **Item 1 (pivot-scale form).** For an arbitrary legal complete pivot `(p, q)`
with nonzero pivot value, every entry of the actual one-step update `pivotSchur`
is bounded by twice the absolute pivot value.  The proof moves the pivot to the
active corner with D10's `movePivot`, applies D11's fixed-corner bound there, and
reads `A p q` back with `movePivot_zero_zero`; ties and negative pivots are
allowed. -/
theorem pivotSchur_entry_abs_le_two_mul_pivot {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p q : Fin (n + 1))
    (hmax : Rho5.Pivot.IsCompletePivot A p q) (hne : A p q ≠ 0) (i j : Fin n) :
    |Rho5.PivotReindex.pivotSchur A p q i j| ≤ 2 * |A p q| := by
  have hmax' : Rho5.Pivot.IsCompletePivot (Rho5.PivotReindex.movePivot A p q) 0 0 :=
    (Rho5.PivotReindex.isCompletePivot_movePivot_iff A p q).mpr hmax
  have hne' : Rho5.PivotReindex.movePivot A p q 0 0 ≠ 0 := by
    rwa [Rho5.PivotReindex.movePivot_zero_zero]
  calc |Rho5.PivotReindex.pivotSchur A p q i j|
      = |Rho5.Pivot.fixedSchur (Rho5.PivotReindex.movePivot A p q) i j| := by
        rw [Rho5.PivotReindex.pivotSchur_eq_fixedSchur]
    _ ≤ 2 * |Rho5.PivotReindex.movePivot A p q 0 0| :=
        Rho5.PivotGrowth.fixedSchur_entry_abs_le_two_mul_pivot _ hmax' hne' i j
    _ = 2 * |A p q| := by rw [Rho5.PivotReindex.movePivot_zero_zero]

/-- **Item 1 (uniform entry bound form).** If in addition every entry of `A` is
bounded by a common `B`, the update entries are bounded by `2 * B`.  This is the
propagation interface used by the stagewise bound below. -/
theorem pivotSchur_entry_abs_le_two_mul_of_entry_bound {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (B : ℝ) (p q : Fin (n + 1))
    (hmax : Rho5.Pivot.IsCompletePivot A p q) (hne : A p q ≠ 0)
    (hB : ∀ i j, |A i j| ≤ B) (i j : Fin n) :
    |Rho5.PivotReindex.pivotSchur A p q i j| ≤ 2 * B := by
  have hmax' : Rho5.Pivot.IsCompletePivot (Rho5.PivotReindex.movePivot A p q) 0 0 :=
    (Rho5.PivotReindex.isCompletePivot_movePivot_iff A p q).mpr hmax
  have hne' : Rho5.PivotReindex.movePivot A p q 0 0 ≠ 0 := by
    rwa [Rho5.PivotReindex.movePivot_zero_zero]
  have hB' : ∀ i j, |Rho5.PivotReindex.movePivot A p q i j| ≤ B := by
    intro i j
    rw [Rho5.PivotReindex.movePivot_apply]
    exact hB _ _
  calc |Rho5.PivotReindex.pivotSchur A p q i j|
      = |Rho5.Pivot.fixedSchur (Rho5.PivotReindex.movePivot A p q) i j| := by
        rw [Rho5.PivotReindex.pivotSchur_eq_fixedSchur]
    _ ≤ 2 * B :=
        Rho5.PivotGrowth.fixedSchur_entry_abs_le_two_mul_of_entry_bound _ B hmax' hne' hB' i j

/-! ## 2. Stagewise `2^k` propagation along any legal trace -/

/-- **Item 2 (stagewise bound predicate).** `ListBoundBy values B` says that the
`k`-th recorded value is at most `2^k * B` for every valid index `k`.  Stated with
`Fin values.length` so that no separate index side condition is needed. -/
def ListBoundBy (values : List ℝ) (B : ℝ) : Prop :=
  ∀ k : Fin values.length, values.get k ≤ (2 : ℝ) ^ (k : ℕ) * B

/-- **Item 2 (one step).** Prepending a value bounded by `B` to a trace whose tail
is bounded stagewise by `2 * B` yields a trace bounded stagewise by `B`: this is
exactly where the factor `2` per stage is paid. -/
theorem listBoundBy_cons {a B : ℝ} (ha : a ≤ B) {tail : List ℝ}
    (ht : ListBoundBy tail (2 * B)) : ListBoundBy (a :: tail) B := by
  intro k
  refine Fin.cases ?_ ?_ k
  · simpa using ha
  · intro j
    have hj : tail.get j ≤ (2 : ℝ) ^ (j : ℕ) * (2 * B) := ht j
    calc (a :: tail).get j.succ = tail.get j := List.get_cons_succ ..
      _ ≤ (2 : ℝ) ^ (j : ℕ) * (2 * B) := hj
      _ = (2 : ℝ) ^ ((j.succ : Fin (tail.length + 1)) : ℕ) * B := by
            rw [Fin.val_succ, pow_succ]
            ring

/-- **Item 2 (the bound).** Along *any* legal trace of `A`, if every entry of the
initial matrix is bounded by `B`, then the `k`-th recorded pivot value is at most
`2^k * B`.  The induction follows the trace constructors: the empty `0 × 0` case has
no entries, the zero-matrix early stop `[0]` only needs `0 ≤ B` (which is the entry
bound at `(0, 0)`), and each genuine step uses item 1 for the update and the
induction hypothesis at `2 * B`.  Nothing assumes a full-rank path, that every step
is nonzero beyond the constructor's own hypothesis, or a unique pivot choice; the
accumulated growth is carried through the exponent rather than re-normalized away. -/
theorem legalTrace_boundBy {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) :
    ∀ {B : ℝ}, (∀ i j, |A i j| ≤ B) → ListBoundBy values B := by
  induction h with
  | empty => intro B hB k; exact Fin.elim0 k
  | zeroStop hzero =>
      intro B hB k
      refine Fin.cases ?_ (fun j => Fin.elim0 j) k
      have h0 : (0 : ℝ) ≤ B := by simpa [hzero] using hB 0 0
      simpa using h0
  | step p q hmax hne htail ih =>
      intro B hB
      exact listBoundBy_cons (hB p q)
        (ih (B := 2 * B)
          (fun i j => pivotSchur_entry_abs_le_two_mul_of_entry_bound _ B p q hmax hne hB i j))

/-! ## 3. Stage maximum and the `Matrix5` sixteen bound -/

/-- **Item 3 (stage maximum).** Every trace value of an `(n+1) × (n+1)` matrix is
bounded by `2^n * stageEntryMax A`: the stagewise bound applies with
`B = stageEntryMax A`, and the index satisfies `k ≤ n`. -/
theorem trace_get_le_pow_mul_stageEntryMax {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) (k : Fin values.length) :
    values.get k ≤ (2 : ℝ) ^ n * Rho5.MatrixStage.stageEntryMax A := by
  have hb := legalTrace_boundBy h (Rho5.MatrixStage.abs_entry_le_stageEntryMax A) k
  have hk : (k : ℕ) ≤ n :=
    Nat.lt_succ_iff.mp (lt_of_lt_of_le k.isLt (Rho5.CompletePivotPath.length_le h))
  have hp : (2 : ℝ) ^ (k : ℕ) ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hk
  calc values.get k ≤ (2 : ℝ) ^ (k : ℕ) * Rho5.MatrixStage.stageEntryMax A := hb
    _ ≤ (2 : ℝ) ^ n * Rho5.MatrixStage.stageEntryMax A :=
        mul_le_mul_of_nonneg_right hp (Rho5.MatrixStage.stageEntryMax_nonneg A)

/-- The `∀ v ∈ values` form of the stage-maximum bound. -/
theorem trace_value_le_pow_mul_stageEntryMax {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) :
    ∀ v ∈ values, v ≤ (2 : ℝ) ^ n * Rho5.MatrixStage.stageEntryMax A := by
  intro v hv
  obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hv
  exact trace_get_le_pow_mul_stageEntryMax A h k

/-- **Item 3 (`Matrix5`, index form).** For the pilot's `5 × 5` matrix every trace
value at index `k` is bounded by `16 * matrixEntryMax A` (the trace has at most five
entries, so `2^k ≤ 2^4 = 16`).  This holds for the zero matrix too, whose trace is
`[0]`. -/
theorem trace_get_le_sixteen (A : Matrix5) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) (k : Fin values.length) :
    values.get k ≤ 16 * matrixEntryMax A := by
  have hb := legalTrace_boundBy h (Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax A) k
  have hk : (k : ℕ) ≤ 4 :=
    Nat.lt_succ_iff.mp (lt_of_lt_of_le k.isLt (Rho5.CompletePivotPath.length_le h))
  have hp : (2 : ℝ) ^ (k : ℕ) ≤ 16 :=
    calc (2 : ℝ) ^ (k : ℕ) ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hk
      _ = 16 := by norm_num
  calc values.get k ≤ (2 : ℝ) ^ (k : ℕ) * matrixEntryMax A := hb
    _ ≤ 16 * matrixEntryMax A :=
        mul_le_mul_of_nonneg_right hp (Rho5.MatrixNormalization.matrixEntryMax_nonneg A)

/-- **Item 3 (`Matrix5`, fixed name).** Every value of every legal trace of a `5 × 5`
matrix is at most `16 * matrixEntryMax A`.  This is a provable coarse bound for all
legal paths; it is not asserted to be optimal, nor equal to the RHO5 constant. -/
theorem trace_value_le_sixteen (A : Matrix5) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) :
    ∀ v ∈ values, v ≤ 16 * matrixEntryMax A := by
  intro v hv
  obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hv
  exact trace_get_le_sixteen A h k

/-- **Item 3 (normalized `Matrix5`).** For a nonzero `5 × 5` matrix, every value of
every legal trace of the *normalized* matrix is at most `16` (D08's
`matrixEntryMax_normalize` gives entry maximum `1`).  The normalization
qualification is derived from `A ≠ 0`, not assumed. -/
theorem normalize_trace_value_le_sixteen (A : Matrix5) (hA : A ≠ 0) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace (Rho5.MatrixNormalization.normalize A) values) :
    ∀ v ∈ values, v ≤ 16 := by
  intro v hv
  have h16 := trace_value_le_sixteen (Rho5.MatrixNormalization.normalize A) h v hv
  rwa [Rho5.MatrixNormalization.matrixEntryMax_normalize A hA, mul_one] at h16

end Rho5.TraceGrowth
