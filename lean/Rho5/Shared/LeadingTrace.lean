/-
D40 — 将任意完整主元路径归约为全程首位置路径
=============================================

The actual pivot-*pattern* reduction of the coverage chain: every real legal trace of
an arbitrary matrix is a trace that only ever pivots at the leading position `(0, 0)`
of *one statically rearranged copy* of the initial matrix.  This removes the dynamic
pivot-position choice; it does not touch the value list, the tie choices, growth, or
any balance/sharpness statement.

Delivered (namespace `Rho5.LeadingTrace`):

1. `LeadingLegalTrace` — the leading trace relation, with the *same* three
   constructors as the frozen D13 `LegalTrace` (`empty` / `zeroStop` / `step`), the
   only difference being that `step`'s pivot is fixed at `(0, 0)` while still
   requiring the real `Rho5.Pivot.IsCompletePivot A 0 0` and a nonzero pivot entry;
   `zeroStop` still records `[0]`.  `legalTrace_of_leading` is the direct one-way
   bridge back to the frozen relation (the original `LegalTrace` is untouched — the
   two are *not* equivalent, which is exactly what goal 3 repairs by a permutation);
2. `liftPerm` — for any tail permutations `σ τ : Equiv.Perm (Fin n)`, the induced
   bijections of `Fin (n+1)` fixing `0` and acting as `σ`/`τ` on the positive
   indices, with `remainingPerm_liftPerm_zero` (the D20 remaining permutation of a
   lifted permutation is the tail permutation itself), `permuteEntries_liftPerm_zero_zero`
   (the top-left entry is preserved) and the **real Schur correspondence**
   `pivotSchur_permuteEntries_liftPerm_zero`:
   `pivotSchur (permuteEntries B (liftPerm ρ) (liftPerm κ)) 0 0
      = permuteEntries (pivotSchur B 0 0) ρ κ`,
   obtained from the frozen D20 `pivotSchur_permuteEntries` — no re-defined transpose
   or Schur operation, and no nonzero-pivot hypothesis (the formula is total, so the
   zero-pivot case is covered);
3. `exists_permute_leadingLegalTrace` — for every real `LegalTrace A values` there
   are *static* `ρ κ : Equiv.Perm (Fin n)` with
   `LeadingLegalTrace (permuteEntries A ρ κ) values`.  The induction follows the real
   path: D10's `movePivot` brings this step's `(p, q)` to `(0, 0)`, the induction
   hypothesis on the tail is lifted by `liftPerm`, and the two are composed into a
   single permutation of the *initial* matrix — the statement is about the original
   matrix rearranged once, not about an abstract sequence of intermediate matrices.
   The value list is kept entrywise (`|A p q|` is exactly the leading entry of the
   rearranged matrix), all tie choices are inherited from the given path, and `n = 0`
   and early zero termination are handled by the `empty`/`zeroStop` cases;
   `exists_submatrix_leadingLegalTrace` is the same statement in the
   `A.submatrix ρ κ` form;
4. `growthRatio_permuteEntries`, `normalize_permuteEntries`,
   `exists_leading_growth_witness`, `exists_leading_normalized_growth_witness` —
   thin adapters over the frozen D20 rearrangement invariance: after the same static
   rearrangement the matrix is still nonzero, `matrixEntryMax` and the real growth
   ratio are unchanged, and a normalized (`matrixEntryMax = 1`) witness keeps unit
   entry maximum.  Hence every real growth witness of a nonzero `Matrix5` has an
   actual matrix representative carrying a leading-only legal trace.

**Scope.**  This removes dynamic pivot-position choice only.  It does **not** claim
that intermediate pivots are positive, that the final `2 × 2` block is automatically
balanced, that B24 covers arbitrary matrices, or that `rho5` is sharp; the explicit
balanced-tail B24 extraction and abstract attainment are other lanes' work.  No
uniqueness of the path and no path existence is claimed.

Read-only frozen inputs (hashes in `INPUT_HASHES.json` and `results/`): pilot
`Rho5.Matrix5`/`Rho5.Pivot`, D08 `MatrixNormalization`, D10 `PivotReindex`,
D12 `MatrixStage` (through D20), D13 `CompletePivotPath`, D17 `GrowthModel`,
D20 `TracePermutation`.  No `sorry`, no new axiom.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixNormalization
import Rho5.Shared.PivotReindex
import Rho5.Shared.CompletePivotPath
import Rho5.Shared.TracePermutation
import Rho5.Shared.GrowthModel

namespace Rho5.LeadingTrace

open Rho5

/-! ## 1. The leading trace relation -/

/-- **Goal 1.**  `LeadingLegalTrace A values` is the frozen D13 legal-trace relation
with the pivot position pinned to the leading corner `(0, 0)`: the same `empty`,
`zeroStop` (still `[0]`) and `step` constructors, and `step` still requires the real
`Rho5.Pivot.IsCompletePivot A 0 0` together with the nonzero pivot entry `A 0 0 ≠ 0`. -/
inductive LeadingLegalTrace : {n : ℕ} → Matrix (Fin n) (Fin n) ℝ → List ℝ → Prop where
  /-- The `0 × 0` matrix: the empty trace. -/
  | empty : LeadingLegalTrace (0 : Matrix (Fin 0) (Fin 0) ℝ) []
  /-- A positive-order zero matrix stops immediately with the single value `0`. -/
  | zeroStop {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hzero : A = 0) :
      LeadingLegalTrace A [0]
  /-- One leading elimination step: a complete pivot *at* `(0, 0)` that is actually
  nonzero, with the frozen D10 Schur update of the leading corner as the tail. -/
  | step {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      (hmax : Rho5.Pivot.IsCompletePivot A 0 0) (hne : A 0 0 ≠ 0) {tail : List ℝ}
      (htail : LeadingLegalTrace (Rho5.PivotReindex.pivotSchur A 0 0) tail) :
      LeadingLegalTrace A (|A 0 0| :: tail)

/-- **Goal 1 (direct bridge).**  Every leading trace is a legal trace of the frozen
D13 relation, with the same value list: the leading `step` is the `step` constructor
at the pivot `(0, 0)`.  The implication is one-way by design — goal 3 supplies the
missing direction after a static rearrangement — so the original relation is neither
modified nor mirrored. -/
theorem legalTrace_of_leading {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ}
    (h : LeadingLegalTrace A values) : Rho5.CompletePivotPath.LegalTrace A values := by
  induction h with
  | empty => exact Rho5.CompletePivotPath.LegalTrace.empty
  | zeroStop hzero => exact Rho5.CompletePivotPath.LegalTrace.zeroStop hzero
  | step hmax hne htail ih => exact Rho5.CompletePivotPath.LegalTrace.step 0 0 hmax hne ih

/-! ## 2. Lifting tail permutations and the leading Schur correspondence -/

/-- **Goal 2 (definition).**  A tail permutation of `Fin n` lifted to `Fin (n+1)`:
`0` stays fixed and the positive index `i.succ` is sent to `(σ i).succ`. -/
def liftPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun i := Fin.cases 0 (fun i' => (σ i').succ) i
  invFun i := Fin.cases 0 (fun i' => (σ.symm i').succ) i
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun i' => ?_) i <;> simp
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun i' => ?_) i <;> simp

@[simp]
theorem liftPerm_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) : liftPerm σ (0 : Fin (n + 1)) = 0 :=
  rfl

@[simp]
theorem liftPerm_succ {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    liftPerm σ i.succ = (σ i).succ :=
  rfl

/-- D10's remaining index at the leading pivot is the successor index. -/
theorem remainingIndex_zero {n : ℕ} (i : Fin n) :
    Rho5.PivotReindex.remainingIndex (0 : Fin (n + 1)) i = i.succ := by
  simp [Rho5.PivotReindex.remainingIndex_apply]

/-- **Goal 2 (remaining permutation).**  The D20 remaining permutation induced by a
lifted tail permutation at the leading pivot is the tail permutation itself. -/
theorem remainingPerm_liftPerm_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Rho5.TracePermutation.remainingPerm (liftPerm σ) (0 : Fin (n + 1)) = σ := by
  apply Equiv.ext
  intro i
  have h := Rho5.TracePermutation.remainingIndex_remainingPerm (liftPerm σ) (0 : Fin (n + 1)) i
  have h' : (Rho5.TracePermutation.remainingPerm (liftPerm σ) (0 : Fin (n + 1)) i).succ
      = (σ i).succ := by
    simpa [liftPerm_zero, remainingIndex_zero, liftPerm_succ] using h
  exact Fin.succ_inj.mp h'

/-- **Goal 2 (top-left entry).**  The lifted rearrangement preserves the leading
entry, so the recorded pivot value is unchanged. -/
theorem permuteEntries_liftPerm_zero_zero {n : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (ρ κ : Equiv.Perm (Fin n)) :
    Rho5.TracePermutation.permuteEntries B (liftPerm ρ) (liftPerm κ) 0 0 = B 0 0 := by
  rw [Rho5.TracePermutation.permuteEntries_apply, liftPerm_zero, liftPerm_zero]

/-- **Goal 2 (completeness at the leading corner).**  The lifted rearrangement
carries complete pivots at the leading corner to complete pivots at the leading
corner, ties included (D20's transport read at `(0, 0)`). -/
theorem isCompletePivot_permuteEntries_liftPerm_iff {n : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (ρ κ : Equiv.Perm (Fin n)) :
    Rho5.Pivot.IsCompletePivot
        (Rho5.TracePermutation.permuteEntries B (liftPerm ρ) (liftPerm κ)) 0 0 ↔
      Rho5.Pivot.IsCompletePivot B 0 0 := by
  rw [Rho5.TracePermutation.isCompletePivot_permuteEntries_iff, liftPerm_zero, liftPerm_zero]

/-- **Goal 2 (the leading Schur correspondence).**  The real D10 `(0, 0)` Schur update
of the lifted rearrangement is exactly the `ρ`/`κ` rearrangement of the original
`(0, 0)` Schur update.  Proved from the frozen D20 `pivotSchur_permuteEntries` plus
goals 2's two computation facts; the formula is total, so no nonzero-pivot hypothesis
is needed. -/
theorem pivotSchur_permuteEntries_liftPerm_zero {n : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (ρ κ : Equiv.Perm (Fin n)) :
    Rho5.PivotReindex.pivotSchur
        (Rho5.TracePermutation.permuteEntries B (liftPerm ρ) (liftPerm κ)) 0 0
      = Rho5.TracePermutation.permuteEntries (Rho5.PivotReindex.pivotSchur B 0 0) ρ κ := by
  rw [Rho5.TracePermutation.pivotSchur_permuteEntries, liftPerm_zero, liftPerm_zero,
    remainingPerm_liftPerm_zero, remainingPerm_liftPerm_zero]

/-! ## 3. Every legal trace is a leading trace of a statically rearranged matrix -/

/-- The leading `(0, 0)` Schur update of the moved matrix is the original one at the
moved pivot `(p, q)`: both are the frozen `Rho5.Pivot.fixedSchur` of `movePivot A p q`. -/
theorem pivotSchur_movePivot_zero_zero_eq {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p q : Fin (n + 1)) :
    Rho5.PivotReindex.pivotSchur (Rho5.PivotReindex.movePivot A p q) 0 0
      = Rho5.PivotReindex.pivotSchur A p q :=
  Rho5.PivotReindex.pivotSchur_movePivot_zero_zero A p q

/-- One leading step for a lifted rearrangement: if the moved matrix has a nonzero
complete pivot at `(0, 0)` and its leading Schur update carries a leading trace of the
tail (in the rearranged form), then the lifted rearrangement carries the leading trace
with `|B 0 0|` as its first recorded value. -/
private theorem leading_step_liftPerm {n : ℕ} {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {tail : List ℝ} (hmax : Rho5.Pivot.IsCompletePivot B 0 0) (hne : B 0 0 ≠ 0)
    {ρ κ : Equiv.Perm (Fin n)}
    (htail : LeadingLegalTrace
      (Rho5.TracePermutation.permuteEntries (Rho5.PivotReindex.pivotSchur B 0 0) ρ κ) tail) :
    LeadingLegalTrace (Rho5.TracePermutation.permuteEntries B (liftPerm ρ) (liftPerm κ))
      (|B 0 0| :: tail) := by
  refine LeadingLegalTrace.step ((isCompletePivot_permuteEntries_liftPerm_iff B ρ κ).mpr hmax)
    ?_ ?_
  · rwa [permuteEntries_liftPerm_zero_zero]
  · rwa [pivotSchur_permuteEntries_liftPerm_zero]

/-- The `step` case of goal 3, stated with the matrix as an explicit parameter so
that the induction can hand over the case's matrix without naming it: D10's `movePivot`
brings `(p, q)` to the corner, the tail's leading trace is lifted by `liftPerm`, and the
two compose into one permutation of `B`. -/
private theorem exists_permute_leading_of_step {n : ℕ}
    {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {p q : Fin (n + 1)} {tail : List ℝ}
    (hmax : Rho5.Pivot.IsCompletePivot B p q) (hne : B p q ≠ 0)
    (ih : ∃ ρ κ : Equiv.Perm (Fin n),
      LeadingLegalTrace (Rho5.TracePermutation.permuteEntries (Rho5.PivotReindex.pivotSchur B p q) ρ κ)
        tail) :
    ∃ ρ κ : Equiv.Perm (Fin (n + 1)),
      LeadingLegalTrace (Rho5.TracePermutation.permuteEntries B ρ κ) (|B p q| :: tail) := by
  obtain ⟨ρ', κ', hlead⟩ := ih
  refine ⟨(liftPerm ρ').trans (Equiv.swap 0 p), (liftPerm κ').trans (Equiv.swap 0 q), ?_⟩
  have hstep := leading_step_liftPerm
    ((Rho5.PivotReindex.isCompletePivot_movePivot_iff B p q).mpr hmax)
    (by rwa [Rho5.PivotReindex.movePivot_zero_zero])
    (by rw [pivotSchur_movePivot_zero_zero_eq]; exact hlead)
  have hmat : Rho5.TracePermutation.permuteEntries B ((liftPerm ρ').trans (Equiv.swap 0 p))
        ((liftPerm κ').trans (Equiv.swap 0 q))
      = Rho5.TracePermutation.permuteEntries (Rho5.PivotReindex.movePivot B p q)
          (liftPerm ρ') (liftPerm κ') := by
    funext i j
    simp [Rho5.TracePermutation.permuteEntries, Rho5.PivotReindex.movePivot,
      Rho5.PivotReindex.reindexEntries]
  rw [hmat, ← Rho5.PivotReindex.movePivot_zero_zero B p q]
  exact hstep

/-- **Goal 3.**  Every real legal trace of an arbitrary `n × n` matrix is a
*leading-only* legal trace (same value list, entrywise) of the initial matrix after
**one static row/column permutation** `ρ`/`κ`.

The induction follows the given real path; a `step` at the pivot `(p, q)` is handled by
`exists_permute_leading_of_step`, which composes D10's `movePivot` with the lifted tail
permutation into a single permutation of the *original* matrix.  The leading entry of
the rearranged matrix is `A p q`, so the recorded list is unchanged; ties, `n = 0` and
the early `zeroStop` are inherited from the given path. -/
theorem exists_permute_leadingLegalTrace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {values : List ℝ} (h : Rho5.CompletePivotPath.LegalTrace A values) :
    ∃ ρ κ : Equiv.Perm (Fin n),
      LeadingLegalTrace (Rho5.TracePermutation.permuteEntries A ρ κ) values := by
  induction h with
  | empty =>
      exact ⟨1, 1, by
        simpa [Rho5.TracePermutation.permuteEntries_zero] using LeadingLegalTrace.empty⟩
  | zeroStop hzero =>
      refine ⟨1, 1, ?_⟩
      rw [hzero, Rho5.TracePermutation.permuteEntries_zero]
      exact LeadingLegalTrace.zeroStop rfl
  | step p q hmax hne htail ih => exact exists_permute_leading_of_step hmax hne ih

/-- **Goal 3 (`submatrix` form).**  The same statement with the rearrangement written
as `A.submatrix ρ κ`; `permuteEntries` *is* `submatrix` by definition. -/
theorem exists_submatrix_leadingLegalTrace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {values : List ℝ} (h : Rho5.CompletePivotPath.LegalTrace A values) :
    ∃ ρ κ : Equiv.Perm (Fin n), LeadingLegalTrace (A.submatrix (⇑ρ) (⇑κ)) values := by
  obtain ⟨ρ, κ, hleading⟩ := exists_permute_leadingLegalTrace h
  exact ⟨ρ, κ, by simpa [Rho5.TracePermutation.permuteEntries] using hleading⟩

/-! ## 4. Growth witnesses with a leading-only path (thin D20 adapters) -/

/-- **Goal 4 (growth ratio).**  The real D17 growth ratio is unchanged by the static
rearrangement: the value list is untouched and D20's entry-max invariance supplies the
denominator. -/
theorem growthRatio_permuteEntries (A : Matrix5) (r c : Equiv.Perm (Fin 5))
    (values : List ℝ) :
    Rho5.GrowthModel.growthRatio (Rho5.TracePermutation.permuteEntries A r c) values
      = Rho5.GrowthModel.growthRatio A values := by
  rw [Rho5.GrowthModel.growthRatio_eq, Rho5.GrowthModel.growthRatio_eq,
    Rho5.TracePermutation.matrixEntryMax_permuteEntries]

/-- **Goal 4 (normalization).**  D08's normalization commutes with the static
rearrangement (D20's invariance, in the form the normalized witness needs). -/
theorem normalize_permuteEntries (A : Matrix5) (r c : Equiv.Perm (Fin 5)) :
    Rho5.MatrixNormalization.normalize (Rho5.TracePermutation.permuteEntries A r c)
      = Rho5.TracePermutation.permuteEntries (Rho5.MatrixNormalization.normalize A) r c :=
  Rho5.TracePermutation.normalize_permuteEntries A r c

/-- **Goal 4 (the nonzero witness).**  Every real growth witness of a nonzero `Matrix5`
has an actual matrix representative — one static rearrangement of the original matrix —
whose legal trace is leading-only, and for which nonzeroness, the D08 entry maximum and
the D17 growth ratio are all unchanged.  Nothing about balance, coverage or sharpness is
claimed. -/
theorem exists_leading_growth_witness {A : Matrix5} {values : List ℝ} {g : ℝ}
    (hA : A ≠ 0) (htrace : Rho5.CompletePivotPath.LegalTrace A values)
    (hg : g = Rho5.GrowthModel.growthRatio A values) :
    ∃ (B : Matrix5) (ρ κ : Equiv.Perm (Fin 5)),
      B = Rho5.TracePermutation.permuteEntries A ρ κ ∧ B ≠ 0 ∧
        matrixEntryMax B = matrixEntryMax A ∧
          g = Rho5.GrowthModel.growthRatio B values ∧ LeadingLegalTrace B values := by
  obtain ⟨ρ, κ, hleading⟩ := exists_permute_leadingLegalTrace htrace
  refine ⟨Rho5.TracePermutation.permuteEntries A ρ κ, ρ, κ, rfl, ?_, ?_, ?_, hleading⟩
  · rwa [Rho5.TracePermutation.permuteEntries_ne_zero_iff]
  · rw [Rho5.TracePermutation.matrixEntryMax_permuteEntries]
  · rw [hg, growthRatio_permuteEntries]

/-- **Goal 4 (the normalized special case).**  If the matrix is normalized
(`matrixEntryMax A = 1`, D17's unit form, where the recorded value is the actual trace
peak), the rearranged representative is again normalized and leading-only, with the same
value. -/
theorem exists_leading_normalized_growth_witness {A : Matrix5} {values : List ℝ} {g : ℝ}
    (hmax : matrixEntryMax A = 1) (htrace : Rho5.CompletePivotPath.LegalTrace A values)
    (hg : g = Rho5.GrowthModel.tracePeak values) :
    ∃ (B : Matrix5) (ρ κ : Equiv.Perm (Fin 5)),
      B = Rho5.TracePermutation.permuteEntries A ρ κ ∧ matrixEntryMax B = 1 ∧
        g = Rho5.GrowthModel.tracePeak values ∧ LeadingLegalTrace B values := by
  obtain ⟨ρ, κ, hleading⟩ := exists_permute_leadingLegalTrace htrace
  exact ⟨Rho5.TracePermutation.permuteEntries A ρ κ, ρ, κ, rfl,
    by rw [Rho5.TracePermutation.matrixEntryMax_permuteEntries, hmax], hg, hleading⟩

end Rho5.LeadingTrace
