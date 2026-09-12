/-
D27 — 实际消元全路径的行列式 / 零终止证书
=============================================

Determinant semantics of the *actual* elimination path: the frozen D10 update
`pivotSchur` at an arbitrary legal nonzero pivot, the induction along D13's real
`LegalTrace`, and the resulting nonsingularity criterion for a given legal path.

Delivered (namespace `Rho5.TraceDeterminant`):

1. `abs_det_eq_abs_pivot_mul_abs_det_pivotSchur` — for the real `pivotSchur` and
   any nonzero pivot entry,
   `|det A| = |A p q| * |det (pivotSchur A p q)|`.
   The row/column transposition `movePivot` preserves the determinant (mathlib's
   `abs_det_submatrix_equiv_equiv`), and the `1 × 1`-block step is mathlib's
   block-determinant API (`det_fromBlocks_zero₂₁` + `det_fromBlocks_one₁₁`, with
   the explicit inverse block `(A 0 0)⁻¹`):
   no hand-rolled cofactor expansion, no `ring` on matrix expansions.  The
   `Invertible`-based `det_fromBlocks₁₁` is deliberately *not* used: there is no
   global `Invertible` instance for the constant `1 × 1` matrix, a local one
   cannot appear in a statement, and `⅟` does not reduce to an explicit matrix
   (verified by the lane's diagnostic probe), so the statement is kept
   `Invertible`-free;
2. `abs_det_eq_prod` — along *every* real `LegalTrace` of an `n × n` matrix the
   absolute determinant is the product of the recorded values,
   `|det A| = values.prod`: an early `zeroStop` contributes its `0` factor and the
   `0 × 0` stage gives the empty product `1` (mathlib's `det_fin_zero` — *not*
   `det 0 = 0`).  `det_eq_zero_of_length_lt` — if the trace is short
   (`values.length < n`) then `det A = 0`.  The length-indexed form of card item 2
   (`values.length = n → |det A| = values.prod`) is the corollary
   `abs_det_eq_prod_of_length_eq`;
3. `det_ne_zero_iff_zero_not_mem` — for a given legal path,
   `det A ≠ 0 ↔ 0 ∉ values`; with `length_eq_of_not_mem_zero` this yields
   `values.length = n` for a nonsingular matrix.  The length-indexed equivalence
   `det_ne_zero_iff_length_eq` carries the *necessary* hypothesis that every
   recorded value be strictly positive (five-stage corollaries for `Matrix5`).

**Card correction (2026-09-12 01:37).**  The original item 3 ("`det A ≠ 0 ↔
values.length = n`" for a path with nonzero recorded values) is *false*: the frozen
D13 `zeroStop` gives the zero `(n+1) × (n+1)` matrix the trace `[0]`, whose length
is `1 = n` for the zero `1 × 1` matrix, while its determinant vanishes.  What is
delivered here is the corrected statement; the strict positivity in
`det_ne_zero_iff_length_eq` is exactly what rules `zeroStop` out.  `LegalTrace`
itself is untouched.

Scope (frozen by the D27 card): everything is relative to a *given* legal path;
no uniqueness of the path, no growth bounds (D15), no path existence (D14), no
determinant/rank statements beyond the above.  Reused unchanged and read-only:
`Rho5.Pivot.fixedSchur`, `Rho5.PivotReindex.{movePivot, pivotSchur}`,
`Rho5.CompletePivotPath.LegalTrace` and mathlib's block-determinant API.

No `sorry`, no new axiom.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.PivotReindex
import Rho5.Shared.CompletePivotPath
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FinCases

namespace Rho5.TraceDeterminant

open Rho5

/-! ## 1. Determinant of one step at an arbitrary nonzero pivot -/

/-- The canonical split of the first index from the remaining ones, tailored to
the plain `Fin (n+1)` indexing of the frozen D08/D10 sources: `0 ↦ inl 0` and
`i.succ ↦ inr i`. -/
private def splitFinEquiv (n : ℕ) : Fin (n + 1) ≃ Fin 1 ⊕ Fin n where
  toFun i := Fin.cases (Sum.inl 0) (fun i' => Sum.inr i') i
  invFun s := Sum.casesOn s (fun _ => 0) (fun i' => i'.succ)
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun i' => ?_) i <;> simp
  right_inv := by
    intro s
    rcases s with i0 | i'
    · fin_cases i0
      simp
    · simp

@[simp]
private theorem splitFinEquiv_zero {n : ℕ} : splitFinEquiv n 0 = Sum.inl 0 := rfl

@[simp]
private theorem splitFinEquiv_succ {n : ℕ} (i : Fin n) :
    splitFinEquiv n i.succ = Sum.inr i := rfl

/-- **Block decomposition.**  A `(n+1) × (n+1)` matrix is its `1 × 1`-block
decomposition along the first row and column, read through `splitFinEquiv`. -/
private theorem blocks_decomposition {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    B = (Matrix.fromBlocks (Matrix.of fun _ _ : Fin 1 => B 0 0)
          (Matrix.of fun (_ : Fin 1) (j : Fin n) => B 0 j.succ)
          (Matrix.of fun (i : Fin n) (_ : Fin 1) => B i.succ 0)
          (Matrix.of fun i j : Fin n => B i.succ j.succ)).submatrix
        (⇑(splitFinEquiv n)) (⇑(splitFinEquiv n)) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.submatrix_apply]

/-- **The `1 × 1`-block Schur determinant**, `Invertible`-free: mathlib's
zero-block formulas applied to the block factorisation of the pivot column, with
the explicit inverse block `fun _ _ => c⁻¹`. -/
private theorem det_fromBlocks_const_finOne {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (B : Matrix (Fin 1) (Fin n) ℝ) (C : Matrix (Fin n) (Fin 1) ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.fromBlocks (Matrix.of fun _ _ : Fin 1 => c) B C D).det
      = c * (D - C * (Matrix.of fun _ _ : Fin 1 => c⁻¹) * B).det := by
  have hCZ : Matrix.of (fun _ _ : Fin 1 => c) * (Matrix.of fun _ _ : Fin 1 => c⁻¹) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Matrix.of_apply, mul_inv_cancel₀ hc]
  have hfac : Matrix.fromBlocks (Matrix.of fun _ _ : Fin 1 => c) B C D
      = Matrix.fromBlocks (Matrix.of fun _ _ : Fin 1 => c) 0 0 1
        * Matrix.fromBlocks 1 ((Matrix.of fun _ _ : Fin 1 => c⁻¹) * B) C D := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Matrix.mul_one, Matrix.zero_mul, add_zero]
    · rw [Matrix.zero_mul, add_zero, ← Matrix.mul_assoc, hCZ, Matrix.one_mul]
    · rw [Matrix.zero_mul, zero_add, Matrix.one_mul]
    · rw [Matrix.zero_mul, zero_add, Matrix.one_mul]
  rw [hfac, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_one₁₁,
    Matrix.det_fin_one, Matrix.det_one, ← Matrix.mul_assoc]
  simp only [Matrix.of_apply, mul_one]

/-- The entrywise Schur complement of a `1 × 1` pivot is exactly the frozen
`Rho5.Pivot.fixedSchur`. -/
private theorem schurBlock_eq_fixedSchur {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (Matrix.of fun i j : Fin n => B i.succ j.succ)
        - (Matrix.of fun (i : Fin n) (_ : Fin 1) => B i.succ 0)
          * (Matrix.of fun _ _ : Fin 1 => (B 0 0)⁻¹)
          * (Matrix.of fun (_ : Fin 1) (j : Fin n) => B 0 j.succ)
      = Rho5.Pivot.fixedSchur B := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_one,
    Rho5.Pivot.fixedSchur, div_eq_mul_inv]
  ring

/-- Moving the pivot to the active corner reindexes rows and columns by two
transpositions, so the determinant is unchanged (mathlib's
`abs_det_submatrix_equiv_equiv`; the statement is kept in absolute values because
the frozen `movePivot` is a `Fin (n+1)` reindexing and not a signed operation). -/
theorem abs_det_movePivot {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) :
    |(Rho5.PivotReindex.movePivot A p q).det| = |A.det| := by
  have h : Rho5.PivotReindex.movePivot A p q
      = A.submatrix (Equiv.swap 0 p) (Equiv.swap 0 q) := rfl
  rw [h]
  exact Matrix.abs_det_submatrix_equiv_equiv _ _ A

/-- Determinant expanded at a nonzero `(0,0)` pivot through mathlib's block
formulas: the `1 × 1` block contributes the pivot and the rest is exactly the
frozen `Rho5.Pivot.fixedSchur`. -/
theorem det_eq_pivot_mul_det_fixedSchur {n : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (h00 : B 0 0 ≠ 0) :
    B.det = B 0 0 * (Rho5.Pivot.fixedSchur B).det := by
  have hdecomp := blocks_decomposition B
  have hdet : ((Matrix.fromBlocks (Matrix.of fun _ _ : Fin 1 => B 0 0)
        (Matrix.of fun (_ : Fin 1) (j : Fin n) => B 0 j.succ)
        (Matrix.of fun (i : Fin n) (_ : Fin 1) => B i.succ 0)
        (Matrix.of fun i j : Fin n => B i.succ j.succ)).submatrix
      (⇑(splitFinEquiv n)) (⇑(splitFinEquiv n))).det
      = (Matrix.fromBlocks (Matrix.of fun _ _ : Fin 1 => B 0 0)
        (Matrix.of fun (_ : Fin 1) (j : Fin n) => B 0 j.succ)
        (Matrix.of fun (i : Fin n) (_ : Fin 1) => B i.succ 0)
        (Matrix.of fun i j : Fin n => B i.succ j.succ)).det :=
    Matrix.det_submatrix_equiv_self (splitFinEquiv n) _
  conv_lhs => rw [hdecomp]
  rw [hdet, det_fromBlocks_const_finOne (B 0 0) h00, schurBlock_eq_fixedSchur B]

/-- **Goal 1.**  For the real one-step update at any nonzero pivot entry, the
absolute determinant scales by the pivot: the permutation is absorbed by the
absolute value, and the block step is the `1 × 1` Schur determinant formula. -/
theorem abs_det_eq_abs_pivot_mul_abs_det_pivotSchur {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p q : Fin (n + 1)) (hne : A p q ≠ 0) :
    |A.det| = |A p q| * |(Rho5.PivotReindex.pivotSchur A p q).det| := by
  have hB : (Rho5.PivotReindex.movePivot A p q) 0 0 ≠ 0 := by
    rwa [Rho5.PivotReindex.movePivot_zero_zero]
  have hschur : (Rho5.PivotReindex.movePivot A p q).det
      = A p q * (Rho5.PivotReindex.pivotSchur A p q).det := by
    rw [Rho5.PivotReindex.pivotSchur, ← Rho5.PivotReindex.movePivot_zero_zero A p q]
    exact det_eq_pivot_mul_det_fixedSchur _ hB
  calc |A.det| = |(Rho5.PivotReindex.movePivot A p q).det| :=
        (abs_det_movePivot A p q).symm
    _ = |A p q| * |(Rho5.PivotReindex.pivotSchur A p q).det| := by
        rw [hschur, abs_mul]

/-- The path-facing form: the completeness qualification of a `LegalTrace` step is
carried explicitly (the identity itself needs only `A p q ≠ 0`). -/
theorem abs_det_eq_abs_pivot_mul_abs_det_pivotSchur_of_isCompletePivot {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p q : Fin (n + 1))
    (_hmax : Rho5.Pivot.IsCompletePivot A p q) (hne : A p q ≠ 0) :
    |A.det| = |A p q| * |(Rho5.PivotReindex.pivotSchur A p q).det| :=
  abs_det_eq_abs_pivot_mul_abs_det_pivotSchur A p q hne

/-! ## 2. Induction along the real legal trace -/

/-- A product of reals vanishes exactly when one factor is `0`. -/
private theorem prod_eq_zero_iff_mem_zero {values : List ℝ} :
    values.prod = 0 ↔ 0 ∈ values := by
  induction values with
  | nil => simp
  | cons v vs ih =>
      rw [List.prod_cons, mul_eq_zero, ih, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h

/-- The determinant of the zero matrix vanishes at positive order.  (Stated with
the order as the argument of `Fin (m+1)` so that it can be used as a rewrite rule
inside the induction, where the case's order is an inaccessible binder.) -/
private theorem det_zero_succ {m : ℕ} :
    (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det = 0 :=
  Matrix.det_zero inferInstance

/-- **Goal 2 (all traces).**  Along *every* real legal trace of an `n × n` matrix
the absolute determinant is the product of the recorded values.  The `0 × 0` case
is `det_fin_zero` (`1 = [].prod`), a zero stop contributes the factor `0` of the
zero matrix at positive order, and each step uses goal 1.  No length hypothesis is
needed: an early stop is paid for by its zero factor. -/
theorem abs_det_eq_prod {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) :
    |A.det| = values.prod := by
  induction h with
  | empty => simp [Matrix.det_fin_zero]
  | zeroStop hzero =>
      rw [hzero, det_zero_succ, abs_zero]
      simp
  | step p q _hmax hne _htail ih =>
      rw [abs_det_eq_abs_pivot_mul_abs_det_pivotSchur _ p q hne, ih, List.prod_cons]

/-- Card item 2, length-indexed form: along a legal trace of full length the
absolute determinant is the product of the recorded values. -/
theorem abs_det_eq_prod_of_length_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {values : List ℝ} (h : Rho5.CompletePivotPath.LegalTrace A values)
    (_hlen : values.length = n) : |A.det| = values.prod :=
  abs_det_eq_prod h

/-- **Goal 2 (short trace).**  If the trace is shorter than the order, the matrix
is singular: `det A = 0`.  A `zeroStop` contributes the single value `0` and the
zero matrix, whose determinant vanishes at positive order. -/
theorem det_eq_zero_of_length_lt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) (hlen : values.length < n) :
    A.det = 0 := by
  induction h with
  | empty => simp at hlen
  | zeroStop hzero => rw [hzero, det_zero_succ]
  | step p q _hmax hne _htail ih =>
      rw [← abs_eq_zero, abs_det_eq_abs_pivot_mul_abs_det_pivotSchur _ p q hne,
        ih (Nat.lt_of_succ_lt_succ hlen), abs_zero, mul_zero]

/-! ## 3. Nonsingularity criterion for a given legal path -/

/-- **Goal 3 (corrected).**  For a *given* legal path, the matrix is nonsingular
exactly when no recorded value is `0` — i.e. exactly when the path never stopped at
a zero pivot.  This is *not* the same as being full: the zero `1 × 1` matrix has the
legal trace `[0]`, of length `1 = n`, and is singular. -/
theorem det_ne_zero_iff_zero_not_mem {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {values : List ℝ} (h : Rho5.CompletePivotPath.LegalTrace A values) :
    A.det ≠ 0 ↔ 0 ∉ values := by
  have habs : |A.det| = values.prod := abs_det_eq_prod h
  constructor
  · intro hdet hmem
    exact hdet (abs_eq_zero.mp (by rw [habs, prod_eq_zero_iff_mem_zero.mpr hmem]))
  · intro hmem hzero
    exact hmem (prod_eq_zero_iff_mem_zero.mp (by rw [← habs, hzero, abs_zero]))

/-- The vanishing companion of `det_ne_zero_iff_zero_not_mem`. -/
theorem det_eq_zero_iff_zero_mem {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) :
    A.det = 0 ↔ 0 ∈ values := by
  constructor
  · intro hzero
    by_contra hmem
    exact ((det_ne_zero_iff_zero_not_mem h).mpr hmem) hzero
  · intro hmem
    by_contra hne
    exact ((det_ne_zero_iff_zero_not_mem h).mp hne) hmem

/-- **Full length of a nonsingular path.**  A legal trace with no zero recorded
value exhausts the order: the only way a path can stop before the order is a
`zeroStop`, which records the value `0`. -/
theorem length_eq_of_not_mem_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) (h0 : 0 ∉ values) :
    values.length = n := by
  induction h with
  | empty => simp
  | zeroStop _hzero => exact absurd (by simp) h0
  | step p q _hmax _hne _htail ih =>
      rw [List.length_cons, ih (fun hmem => h0 (List.mem_cons_of_mem _ hmem))]

/-- **Goal 3, length-indexed form.**  For a legal path all of whose recorded values
are strictly positive (in particular none is `0`), the matrix is nonsingular
exactly when the trace is full.  Strict positivity is necessary: `[0]` is a legal
trace of the zero `1 × 1` matrix, and the trace `[v₁, 0]` of a `2 × 2` matrix has
full length with a vanishing last value. -/
theorem det_ne_zero_iff_length_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) (hpos : ∀ v ∈ values, 0 < v) :
    A.det ≠ 0 ↔ values.length = n := by
  constructor
  · intro hdet
    exact length_eq_of_not_mem_zero h fun hmem => absurd (hpos 0 hmem) (lt_irrefl 0)
  · intro _hlen
    rw [det_ne_zero_iff_zero_not_mem h]
    intro hmem
    exact absurd (hpos 0 hmem) (lt_irrefl 0)

/-- **Five-stage corollary (corrected).**  For the pilot's `5 × 5` matrix, a legal
trace with no zero recorded value certifies nonsingularity, and nonsingularity
forces every recorded value to be nonzero. -/
theorem det_ne_zero_iff_zero_not_mem_five {A : Matrix5} {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) :
    A.det ≠ 0 ↔ 0 ∉ values :=
  det_ne_zero_iff_zero_not_mem h

/-- **Five-stage corollary.**  With all recorded values strictly positive, a legal
trace of the pilot's `5 × 5` matrix is full exactly when the matrix is
nonsingular. -/
theorem det_ne_zero_iff_length_eq_five {A : Matrix5} {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) (hpos : ∀ v ∈ values, 0 < v) :
    A.det ≠ 0 ↔ values.length = 5 :=
  det_ne_zero_iff_length_eq h hpos

/-- The full-length form of the five-stage corollary: along a full legal trace of
a `5 × 5` matrix, `|det A|` is the product of the recorded pivot values. -/
theorem abs_det_eq_prod_of_length_eq_five {A : Matrix5} {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) (_hlen : values.length = 5) :
    |A.det| = values.prod :=
  abs_det_eq_prod h

end Rho5.TraceDeterminant
