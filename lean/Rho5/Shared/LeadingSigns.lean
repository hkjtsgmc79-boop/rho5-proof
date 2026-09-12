/-
D41 — 首位置路径的前四个主元符号规范化
=====================================

Static *row-sign* normalization of a leading-only path: the sign of a pivot can be
fixed by flipping the sign of the corresponding original row, and flipping the first
row leaves the real `(0,0)` Schur update untouched while multiplying the corner pivot
by the sign.  This removes the sign obstruction of the normalized matrix
representative; the last `1 × 1` pivot is deliberately **not** forced positive.

Delivered (namespace `Rho5.LeadingSigns`):

1. `pivotSchur_signedEntries_rows` — the real D10 `pivotSchur` at `(0, 0)` under row
   signs: the leading sign cancels and the tail signs are carried onto the rows of the
   Schur update.  The formula is *unconditional in the denominator* (real division is
   total; only `σ * σ = 1`, i.e. the sign being `±1`, is used); D22's general two-sided
   `pivotSchur_signedEntries` instead assumes the pivot entry nonzero, which is what a
   legal step provides anyway.  `pivotSchur_firstRowSign` (Schur unchanged; corner pivot
   `ε * A 0 0`) and `pivotSchur_liftTailSign` (Schur is the same tail row-sign
   transform) are the two specializations asked for by the card; D22's full-path sign
   invariance is reused, not re-proved;
2. `LeadingTracePos` — the auxiliary leading-path relation carrying the prefix
   positivity: `step` records a strictly positive pivot, `lastStep` is the final
   `1 × 1` level (sign `+1`, pivot *not* forced positive), and `zeroStop`/`empty` are
   as in D40.  `leadingLegalTrace_of_leadingTracePos` is the bridge back to D40's
   `LeadingLegalTrace`; `exists_signs_leadingTracePos` constructs, for *every* leading
   trace, static signs `s` with `IsSign s` such that the signed matrix has the same
   value list and every pivot except the last `1 × 1` one (and except the zero pivot of
   an early `zeroStop`) is positive.  The construction decides the sign of level `k`
   from the pivot of level `k` (and keeps the last row's sign `+1`);
3. `leadingTrace_smul` and `exists_normalized_leading_sign_witness` — the concrete
   five-stage representative: for a nonzero `Matrix5` and each real `LegalTrace`, one
   static D40 row/column permutation, the D08 normalization by a positive scalar `c`,
   and one static row-sign vector produce a real `Matrix5` `B` with
   `matrixEntryMax B = 1`, `B 0 0 = 1`, a leading trace with the normalized value list
   `values.map (fun v => c * v)` whose pivots are positive except the last `1 × 1` one,
   and the *same* D17 growth ratio as the original witness.

**Scope / non-claims.**  Sign normalization only removes the sign obstruction: it does
**not** produce B24's balanced tail blocks, does **not** claim `s`/`t` nonnegativity, no
alpha bound and no attainment.  Early stopping is kept explicit: no full-rank and no
five-nonzero-pivot assumption is made, and the zero pivot of an early `zeroStop` is not
claimed positive.  A downstream full-length version would additionally need
`values.length = 5` (i.e. no early stop) as an explicit hypothesis.

Read-only frozen inputs (hashes in `INPUT_HASHES.json` / `results/`): pilot
`Rho5.Matrix5`/`Rho5.Pivot`, D08 `MatrixNormalization`, D10 `PivotReindex`,
D12 `MatrixStage`, D13 `CompletePivotPath`, D17 `GrowthModel`, D20 `TracePermutation`,
D22 `TraceSigns`, D40 `LeadingTrace`.  No `sorry`, no new axiom.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixNormalization
import Rho5.Shared.PivotReindex
import Rho5.Shared.CompletePivotPath
import Rho5.Shared.TracePermutation
import Rho5.Shared.TraceSigns
import Rho5.Shared.TraceSigns.GrowthAdapter
import Rho5.Shared.GrowthModel
import Rho5.Shared.LeadingTrace

namespace Rho5.LeadingSigns

open Rho5

/-! ## 1. Row signs and the real `(0, 0)` Schur update -/

/-- A sign factor cancels in a quotient: `w * (σ * y) / (σ * z) = w * (y / z)`.  Only
`σ * σ = 1` is used, so no hypothesis on the denominator `z` is needed (real division is
total). -/
private theorem sign_div_cancel (σ w y z : ℝ) (hσ : σ * σ = 1) :
    w * (σ * y) / (σ * z) = w * (y / z) := by
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, hσinv]
  rw [show w * (σ * y) * (z⁻¹ * σ) = (σ * σ) * (w * (y * z⁻¹)) by ring, hσ, one_mul]

/-- **Goal 1 (general row-sign formula).**  The real D10 `pivotSchur` at `(0, 0)`
under row signs: the leading sign cancels out, the tail signs are carried onto the
rows of the Schur update.  No nonzero hypothesis on `A 0 0` is needed. -/
theorem pivotSchur_signedEntries_rows {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {s : Fin (n + 1) → ℝ} (hs : Rho5.TraceSigns.IsSign s) :
    Rho5.PivotReindex.pivotSchur (Rho5.TraceSigns.signedEntries A s 1) 0 0
      = Rho5.TraceSigns.signedEntries (Rho5.PivotReindex.pivotSchur A 0 0)
          (fun i => s i.succ) 1 := by
  funext i j
  simp only [Rho5.PivotReindex.pivotSchur_apply, Rho5.LeadingTrace.remainingIndex_zero,
    Rho5.TraceSigns.signedEntries_apply, Pi.one_apply, one_mul, mul_one]
  rw [sign_div_cancel (s 0) (s i.succ * A i.succ 0) (A 0 j.succ) (A 0 0) (hs.mul_self 0)]
  ring

/-- Signing by the constant `1` returns the matrix. -/
theorem signedEntries_const_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Rho5.TraceSigns.signedEntries A (fun _ => 1) 1 = A := by
  funext i j
  simp [Rho5.TraceSigns.signedEntries_apply]

/-- The row-sign vector flipping only the first row by `ε`. -/
theorem signedEntries_one_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Rho5.TraceSigns.signedEntries A 1 1 = A := by
  funext i j
  simp [Rho5.TraceSigns.signedEntries_apply]

/-- Signing the zero matrix keeps it zero (used by the `zeroStop` cases). -/
theorem signedEntries_zero_matrix {n : ℕ} (s : Fin n → ℝ) :
    Rho5.TraceSigns.signedEntries (0 : Matrix (Fin n) (Fin n) ℝ) s 1 = 0 := by
  funext i j
  simp [Rho5.TraceSigns.signedEntries_apply]

/-- The row-sign vector flipping only the first row by `ε`. -/
def firstRowSign {n : ℕ} (ε : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases ε fun _ => 1

@[simp]
theorem firstRowSign_zero {n : ℕ} (ε : ℝ) : firstRowSign (n := n) ε 0 = ε := rfl

@[simp]
theorem firstRowSign_succ {n : ℕ} (ε : ℝ) (i : Fin n) : firstRowSign (n := n) ε i.succ = 1 := rfl

/-- Lifting tail signs to `Fin (n+1)` with leading sign `+1`. -/
def liftTailSign {n : ℕ} (s : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases 1 s

@[simp]
theorem liftTailSign_zero {n : ℕ} (s : Fin n → ℝ) : liftTailSign s (0 : Fin (n + 1)) = 1 := rfl

@[simp]
theorem liftTailSign_succ {n : ℕ} (s : Fin n → ℝ) (i : Fin n) : liftTailSign s i.succ = s i := rfl

theorem isSign_firstRowSign {n : ℕ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Rho5.TraceSigns.IsSign (firstRowSign (n := n) ε) := by
  intro i
  refine Fin.cases ?_ (fun i' => ?_) i
  · simpa using hε
  · exact Or.inl rfl

theorem isSign_liftTailSign {n : ℕ} {s : Fin n → ℝ} (hs : Rho5.TraceSigns.IsSign s) :
    Rho5.TraceSigns.IsSign (liftTailSign s) := by
  intro i
  refine Fin.cases ?_ (fun i' => ?_) i
  · exact Or.inl rfl
  · exact hs i'

/-- **Goal 1 (first row).**  Multiplying the first row by `ε = ±1` leaves the real
`(0, 0)` Schur update unchanged, while the corner pivot becomes `ε * A 0 0`.  The
formula needs no hypothesis on `A 0 0`; making the pivot *positive* requires
`A 0 0 ≠ 0` (see `exists_signs_leadingTracePos`). -/
theorem pivotSchur_firstRowSign {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    Rho5.PivotReindex.pivotSchur (Rho5.TraceSigns.signedEntries A (firstRowSign (n := n) ε) 1) 0 0
      = Rho5.PivotReindex.pivotSchur A 0 0 := by
  rw [pivotSchur_signedEntries_rows A (isSign_firstRowSign hε)]
  exact signedEntries_const_one _

/-- **Goal 1 (corner pivot).**  The corner pivot of the first-row-signed matrix. -/
theorem firstRowSign_pivot {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (ε : ℝ) :
    Rho5.TraceSigns.signedEntries A (firstRowSign (n := n) ε) 1 0 0 = ε * A 0 0 := by
  simp [Rho5.TraceSigns.signedEntries_apply]

/-- **Goal 1 (tail signs).**  Lifting tail signs (leading sign `+1`) makes the real
`(0, 0)` Schur update the *same* tail row-sign transform of the original update. -/
theorem pivotSchur_liftTailSign {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {s : Fin n → ℝ} (hs : Rho5.TraceSigns.IsSign s) :
    Rho5.PivotReindex.pivotSchur (Rho5.TraceSigns.signedEntries A (liftTailSign s) 1) 0 0
      = Rho5.TraceSigns.signedEntries (Rho5.PivotReindex.pivotSchur A 0 0) s 1 := by
  simpa using pivotSchur_signedEntries_rows A (isSign_liftTailSign hs)

/-! ## 2. The positivity-carrying auxiliary relation and the sign construction -/

/-- **Goal 2 (auxiliary relation).**  A leading-only path with prefix positivity:
`step` records a strictly positive pivot, `lastStep` is the final `1 × 1` level whose
sign is `+1` and whose pivot is *not* forced positive, and `empty`/`zeroStop` are as in
D40 (an early `zeroStop` keeps its zero pivot, which is not claimed positive). -/
inductive LeadingTracePos : {n : ℕ} → Matrix (Fin n) (Fin n) ℝ → List ℝ → Prop where
  /-- The `0 × 0` matrix: the empty trace. -/
  | empty : LeadingTracePos (0 : Matrix (Fin 0) (Fin 0) ℝ) []
  /-- A positive-order zero matrix stops with the single value `0`. -/
  | zeroStop {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hzero : A = 0) :
      LeadingTracePos A [0]
  /-- One leading step whose pivot is strictly positive. -/
  | step {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      (hmax : Rho5.Pivot.IsCompletePivot A 0 0) (hne : A 0 0 ≠ 0) (hpos : 0 < A 0 0)
      {tail : List ℝ} (htail : LeadingTracePos (Rho5.PivotReindex.pivotSchur A 0 0) tail) :
      LeadingTracePos A (A 0 0 :: tail)
  /-- The final `1 × 1` level: legal and nonzero, but the pivot is not forced positive. -/
  | lastStep {A : Matrix (Fin 1) (Fin 1) ℝ} (hmax : Rho5.Pivot.IsCompletePivot A 0 0)
      (hne : A 0 0 ≠ 0) : LeadingTracePos A [|A 0 0|]

/-- The unique `0 × 0` matrix is zero (needed to terminate a leading path). -/
private theorem matrix_fin_zero_eq_zero (A : Matrix (Fin 0) (Fin 0) ℝ) : A = 0 := by
  funext i
  exact Fin.elim0 i

/-- **Goal 2 (bridge to D40).**  The positivity-carrying relation is a sub-relation of
D40's `LeadingLegalTrace`, with the same value list (`A 0 0 = |A 0 0|` on positive
steps; `lastStep` is the `1 × 1` instance of `step`). -/
theorem leadingLegalTrace_of_leadingTracePos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {values : List ℝ} (h : LeadingTracePos A values) :
    Rho5.LeadingTrace.LeadingLegalTrace A values := by
  induction h with
  | empty => exact Rho5.LeadingTrace.LeadingLegalTrace.empty
  | zeroStop hzero => exact Rho5.LeadingTrace.LeadingLegalTrace.zeroStop hzero
  | step hmax hne hpos htail ih =>
      simpa [abs_of_pos hpos] using Rho5.LeadingTrace.LeadingLegalTrace.step hmax hne ih
  | lastStep hmax hne =>
      refine Rho5.LeadingTrace.LeadingLegalTrace.step hmax hne ?_
      rw [show Rho5.PivotReindex.pivotSchur _ 0 0 = 0 from matrix_fin_zero_eq_zero _]
      exact Rho5.LeadingTrace.LeadingLegalTrace.empty

/-- A leading trace of a `0 × 0` matrix is the empty trace of the zero matrix. -/
theorem leadingLegalTrace_fin_zero {A : Matrix (Fin 0) (Fin 0) ℝ} {values : List ℝ}
    (h : Rho5.LeadingTrace.LeadingLegalTrace A values) : A = 0 ∧ values = [] := by
  cases h with
  | empty => exact ⟨rfl, rfl⟩

/-- **Goal 2 (construction).**  Every real leading trace has static row signs `s` with
`IsSign s` such that the signed matrix carries a positivity-carrying leading trace with
the *same* value list: every step pivot is positive, the final `1 × 1` pivot is left
alone, and the last original row keeps sign `+1`.  The recursion follows the order:
at order ≥ 2 the sign of the current level is chosen to make the pivot positive, at
order 1 the sign is `+1`. -/
theorem exists_signs_leadingTracePos :
    ∀ {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ},
      Rho5.LeadingTrace.LeadingLegalTrace B values →
        ∃ s : Fin n → ℝ, Rho5.TraceSigns.IsSign s ∧
          LeadingTracePos (Rho5.TraceSigns.signedEntries B s 1) values
  | 0, B, values, h => by
      cases h with
      | empty =>
          refine ⟨fun i => Fin.elim0 i, (fun i => Fin.elim0 i), ?_⟩
          rw [show Rho5.TraceSigns.signedEntries (0 : Matrix (Fin 0) (Fin 0) ℝ)
                (fun i => Fin.elim0 i) 1 = 0 from signedEntries_zero_matrix _]
          exact LeadingTracePos.empty
  | n + 1, B, values, h => by
      cases h with
      | zeroStop hzero =>
          refine ⟨fun _ => 1, (fun i => Or.inl rfl), ?_⟩
          rw [hzero, signedEntries_zero_matrix]
          exact LeadingTracePos.zeroStop rfl
      | step hmax hne htail =>
          match n with
          | 0 =>
              -- the last `1 × 1` level: sign `+1`, pivot not forced positive
              refine ⟨fun _ => 1, (fun i => Or.inl rfl), ?_⟩
              have hnil := leadingLegalTrace_fin_zero htail
              obtain ⟨-, rfl⟩ := hnil
              simpa [signedEntries_one_one] using
                LeadingTracePos.lastStep (A := Rho5.TraceSigns.signedEntries B (fun _ => 1) 1)
                  ((Rho5.TraceSigns.isCompletePivot_signedEntries_iff B (r := fun _ => 1)
                    (c := fun _ => 1) (fun i => Or.inl rfl) (fun i => Or.inl rfl) 0 0).mpr hmax)
                  (by simpa [signedEntries_one_one] using hne)
          | k + 1 =>
              obtain ⟨s', hs', htail'⟩ := exists_signs_leadingTracePos htail
              let svec : Fin (k + 2) → ℝ := Fin.cases (if 0 < B 0 0 then (1 : ℝ) else -1) s'
              refine ⟨svec, ?_, ?_⟩
              · intro i
                refine Fin.cases ?_ (fun i' => ?_) i
                · dsimp only [svec]; split_ifs <;> simp
                · exact hs' i'
              · have hpiv : Rho5.TraceSigns.signedEntries B svec 1 0 0 = |B 0 0| := by
                  dsimp only [svec]
                  simp only [Rho5.TraceSigns.signedEntries_apply, Fin.cases_zero, Pi.one_apply]
                  split_ifs with h
                  · rw [one_mul, mul_one, abs_of_pos h]
                  · rw [neg_one_mul, mul_one, abs_of_neg (lt_of_le_of_ne (le_of_not_gt h) hne)]
                have hsvec : Rho5.TraceSigns.IsSign svec := by
                  intro i
                  refine Fin.cases ?_ (fun i' => ?_) i
                  · dsimp only [svec]; split_ifs <;> simp
                  · exact hs' i'
                have hpos : 0 < Rho5.TraceSigns.signedEntries B svec 1 0 0 := by
                  rw [hpiv]; exact abs_pos.mpr hne
                have hschur : Rho5.PivotReindex.pivotSchur (Rho5.TraceSigns.signedEntries B svec 1) 0 0
                    = Rho5.TraceSigns.signedEntries (Rho5.PivotReindex.pivotSchur B 0 0) s' 1 := by
                  have h := pivotSchur_signedEntries_rows B (s := svec) hsvec
                  simpa only [svec, Fin.cases_succ] using h
                have hmax' : Rho5.Pivot.IsCompletePivot (Rho5.TraceSigns.signedEntries B svec 1) 0 0 :=
                  (Rho5.TraceSigns.isCompletePivot_signedEntries_iff B (r := svec) (c := fun _ => 1)
                    hsvec (fun i => Or.inl rfl) 0 0).mpr hmax
                have hne' : Rho5.TraceSigns.signedEntries B svec 1 0 0 ≠ 0 := by
                  rw [hpiv]; exact abs_ne_zero.mpr hne
                rw [← hpiv]
                refine LeadingTracePos.step hmax' hne' hpos ?_
                rw [hschur]; exact htail'

end Rho5.LeadingSigns
