/-
D36 — 全路径转置对称性
=======================

Transposition symmetry of the *actual* elimination path, stated on the frozen
objects only: the real complete-pivot predicate, the real D10 `pivotSchur` update,
the real D13 `LegalTrace`, D17's real `growthRatio`, and D23's first-pivot `+1`
normalized domain.  No second transposed Schur definition, no re-proof of the
existing permutation/sign work, no new norm or pivot predicate.

Delivered (namespace `Rho5.TraceTranspose`):

1. `isCompletePivot_transpose_iff` — `IsCompletePivot A p q ↔ IsCompletePivot Aᵀ q p`
   (the predicate is a plain `∀ i j, |A i j| ≤ |A p q|`, so the two sides are the
   same statement read on transposed indices);
   `pivotSchur_transpose` — `pivotSchur Aᵀ q p = (pivotSchur A p q)ᵀ`, proved
   **directly from the frozen D10 `remainingIndex` entry formula**
   (`Rho5.PivotReindex.pivotSchur_apply`), not from any re-defined transpose Schur
   complement.  The identity is total: *no* nonzero-pivot hypothesis is needed, so
   the zero-pivot case is covered as well;
2. `legalTrace_transpose` / `legalTrace_transpose_iff` — for every matrix,
   `LegalTrace A values ↔ LegalTrace Aᵀ values` with the **same list** `values`,
   hence the same tie choices, the same `|A p q|` entries and the same
   `zeroStop = [0]`; `empty` is the `0 × 0` case.  The forward direction is the
   induction on the real path, the backward direction is the forward direction at
   `Aᵀ` followed by `Matrix.transpose_transpose` — no invertibility hypothesis
   anywhere;
3. entry-max / nonzero / normalization transport and the real growth ratio:
   `matrixEntryMax_transpose`, `transpose_eq_zero_iff`, `transpose_ne_zero_iff`,
   `normalize_transpose`, `growthRatio_transpose`, plus the **callable witness
   adapters** `growthValues_transpose_witness` and
   `normalizedGrowthValues_transpose_witness`, which transport an actual growth
   witness *for a given `(A, values)`* to `(Aᵀ, values)` (deliberately not the
   trivial whole-set self-equality of `GrowthValues`);
4. first-pivot `+1` domain: `firstPivot_transpose_witness` transports a witness of
   D23's `FirstPivotGrowthValues` conditions — `matrixEntryMax A = 1`, `A 0 0 = 1`,
   `IsCompletePivot A 0 0`, a real legal trace and the growth-ratio value — to the
   transposed matrix, using `transpose_zero_zero`, `matrixEntryMax_transpose`,
   `isCompletePivot_transpose_iff`, `legalTrace_transpose_iff` and
   `growthRatio_transpose`.

**Scope / non-claims.**  Everything is relative to the given matrices and their
given legal paths.  Transposition symmetry does **not** say that B24 covers an
arbitrary matrix, does not give a global sharp bound, and does not say that any
`alpha` is attained; growth bounds and endpoint statements remain where D17/D23/D25
put them.  No path uniqueness and no path existence is claimed.

Read-only frozen inputs (hashes in `INPUT_HASHES.json` / `results/`): pilot
`Rho5.Matrix5`/`matrixEntryMax`/`Rho5.Pivot`, D08 `MatrixNormalization`, D10
`PivotReindex`, D13 `CompletePivotPath`, D17 `GrowthModel`, D20 `TracePermutation`
(through D23), D23 `FirstPivotDomain`.  No `sorry`, no new axiom.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixNormalization
import Rho5.Shared.PivotReindex
import Rho5.Shared.CompletePivotPath
import Rho5.Shared.GrowthModel
import Rho5.Shared.FirstPivotDomain

namespace Rho5.TraceTranspose

open Rho5

open scoped Matrix

/-! ## 1. Complete pivots and the real Schur update under transposition -/

/-- **Goal 1 (predicate).**  The frozen complete-pivot predicate is transpose
symmetric with the two indices exchanged: both sides say that every entry of `A`
is bounded in absolute value by the pivot entry. -/
theorem isCompletePivot_transpose_iff {ι κ : Type*} (A : Matrix ι κ ℝ) (p : ι) (q : κ) :
    Rho5.Pivot.IsCompletePivot A p q ↔ Rho5.Pivot.IsCompletePivot Aᵀ q p := by
  constructor
  · intro h i j
    simpa using h j i
  · intro h i j
    simpa using h j i

/-- **Goal 1 (one step).**  The frozen D10 update commutes with transposition at
the exchanged pivot: `pivotSchur Aᵀ q p = (pivotSchur A p q)ᵀ`.

This is checked **entrywise against the frozen `remainingIndex` formula**
(`Rho5.PivotReindex.pivotSchur_apply`), i.e. on the original definition rather than
on a re-defined transposed Schur complement.  The statement is total in the pivot
entry: it holds for `A p q = 0` as well, where the expression is defined by real
division. -/
theorem pivotSchur_transpose {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) :
    Rho5.PivotReindex.pivotSchur Aᵀ q p = (Rho5.PivotReindex.pivotSchur A p q)ᵀ := by
  ext i j
  simp only [Rho5.PivotReindex.pivotSchur_apply, Matrix.transpose_apply, div_eq_mul_inv]
  ring

/-! ## 2. The full legal trace, including every tie choice and `zeroStop` -/

/-- **Goal 2 (forward).**  The transposed matrix has the same legal trace, with the
*same* list of recorded values: the pivot moves from `(p, q)` to `(q, p)`, the
completeness qualification is goal 1, the nonzero pivot entry is unchanged, and the
tail is the transposed Schur update.  A `zeroStop` stays `[0]` and the `0 × 0`
`empty` trace is the empty list. -/
theorem legalTrace_transpose {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) :
    Rho5.CompletePivotPath.LegalTrace Aᵀ values := by
  induction h with
  | empty => simpa using Rho5.CompletePivotPath.LegalTrace.empty
  | zeroStop hzero =>
      rw [hzero, Matrix.transpose_zero]
      exact Rho5.CompletePivotPath.LegalTrace.zeroStop rfl
  | step p q hmax hne htail ih =>
      exact Rho5.CompletePivotPath.LegalTrace.step q p
        ((isCompletePivot_transpose_iff _ p q).mp hmax)
        (by simpa [Matrix.transpose_apply] using hne)
        (by rw [pivotSchur_transpose]; exact ih)

/-- **Goal 2 (iff).**  Transposition neither creates nor destroys legal traces; the
backward direction is the forward direction applied at `Aᵀ` together with
`Matrix.transpose_transpose`, so no invertibility of `A` (or of anything else) is
assumed. -/
theorem legalTrace_transpose_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ} :
    Rho5.CompletePivotPath.LegalTrace A values ↔
      Rho5.CompletePivotPath.LegalTrace Aᵀ values :=
  ⟨legalTrace_transpose, fun h => by
    have h' := legalTrace_transpose (A := Aᵀ) h
    rwa [Matrix.transpose_transpose] at h'⟩

/-! ## 3. Entry max, nonzero / normalization transport, growth ratio -/

/-- **Goal 3 (entry max).**  The frozen entry maximum is transpose invariant: the
25 index positions are permuted by `(i, j) ↦ (j, i)`. -/
theorem matrixEntryMax_transpose (M : Matrix5) : matrixEntryMax Mᵀ = matrixEntryMax M := by
  apply le_antisymm
  · rw [matrixEntryMax, matrixEntryMax]
    refine Finset.sup'_le Finset.univ_nonempty (fun ij : Fin 5 × Fin 5 => |Mᵀ ij.1 ij.2|)
      (fun ij _ => ?_)
    exact Finset.le_sup' (f := fun ij : Fin 5 × Fin 5 => |M ij.1 ij.2|)
      (Finset.mem_univ (ij.2, ij.1))
  · rw [matrixEntryMax, matrixEntryMax]
    refine Finset.sup'_le Finset.univ_nonempty (fun ij : Fin 5 × Fin 5 => |M ij.1 ij.2|)
      (fun ij _ => ?_)
    exact Finset.le_sup' (f := fun ij : Fin 5 × Fin 5 => |Mᵀ ij.1 ij.2|)
      (Finset.mem_univ (ij.2, ij.1))

/-- **Goal 3 (nonzero transport).**  Vanishing is transpose invariant. -/
theorem transpose_eq_zero_iff (M : Matrix5) : Mᵀ = 0 ↔ M = 0 := by
  constructor
  · intro h
    have h' := congrArg Matrix.transpose h
    rwa [Matrix.transpose_transpose, Matrix.transpose_zero] at h'
  · intro h
    rw [h, Matrix.transpose_zero]

/-- **Goal 3 (nonzero transport).**  Non-vanishing is transpose invariant, in the
form used by the growth sets. -/
theorem transpose_ne_zero_iff (M : Matrix5) : Mᵀ ≠ 0 ↔ M ≠ 0 := by
  rw [ne_eq, ne_eq, transpose_eq_zero_iff]

/-- **Goal 3 (normalization transport).**  D08's normalization commutes with
transposition, because the scaling factor `matrixEntryMax` is transpose invariant
and scalar multiplication commutes with transposition. -/
theorem normalize_transpose (M : Matrix5) :
    Rho5.MatrixNormalization.normalize Mᵀ = (Rho5.MatrixNormalization.normalize M)ᵀ := by
  rw [Rho5.MatrixNormalization.normalize_eq_inv_smul,
    Rho5.MatrixNormalization.normalize_eq_inv_smul, matrixEntryMax_transpose,
    Matrix.transpose_smul]

/-- **Goal 3 (growth ratio).**  D17's real growth ratio is transpose invariant: the
recorded list is untouched and the denominator is goal 3's entry maximum. -/
theorem growthRatio_transpose (A : Matrix5) (values : List ℝ) :
    Rho5.GrowthModel.growthRatio Aᵀ values = Rho5.GrowthModel.growthRatio A values := by
  rw [Rho5.GrowthModel.growthRatio_eq, Rho5.GrowthModel.growthRatio_eq, matrixEntryMax_transpose]

/-- **Goal 3 (callable witness adapter).**  A genuine growth witness for a *given*
pair `(A, values)` — nonzero matrix, real legal trace, and the recorded value `g`
equal to the actual growth ratio — transports to the transposed pair
`(Aᵀ, values)`.  This is the pair-level adapter, not the trivial self-equality of
the whole set `GrowthValues`. -/
theorem growthValues_transpose_witness {A : Matrix5} {values : List ℝ} {g : ℝ}
    (hA : A ≠ 0) (htrace : Rho5.CompletePivotPath.LegalTrace A values)
    (hg : g = Rho5.GrowthModel.growthRatio A values) :
    Aᵀ ≠ 0 ∧ Rho5.CompletePivotPath.LegalTrace Aᵀ values ∧
      g = Rho5.GrowthModel.growthRatio Aᵀ values :=
  ⟨(transpose_ne_zero_iff A).mpr hA, (legalTrace_transpose_iff).mpr htrace,
    by rw [hg, growthRatio_transpose]⟩

/-- **Goal 3 (normalized witness adapter).**  The unit-entry-max normalized form of
the same witness: `matrixEntryMax A = 1` and the value is the actual trace peak.
Transporting it needs only the entry-max invariance and the trace transfer — the
peak itself is a function of the list alone. -/
theorem normalizedGrowthValues_transpose_witness {A : Matrix5} {values : List ℝ} {g : ℝ}
    (hmax : matrixEntryMax A = 1) (htrace : Rho5.CompletePivotPath.LegalTrace A values)
    (hg : g = Rho5.GrowthModel.tracePeak values) :
    matrixEntryMax Aᵀ = 1 ∧ Rho5.CompletePivotPath.LegalTrace Aᵀ values ∧
      g = Rho5.GrowthModel.tracePeak values :=
  ⟨by rw [matrixEntryMax_transpose, hmax], (legalTrace_transpose_iff).mpr htrace, hg⟩

/-! ## 4. The first-pivot `+1` normalized domain under transposition -/

/-- **Goal 4 (domain conditions).**  `A 0 0 = 1` is transpose invariant: the corner
entry is the same entry. -/
theorem transpose_zero_zero (A : Matrix5) : Aᵀ 0 0 = A 0 0 :=
  Matrix.transpose_apply A 0 0

/-- **Goal 4 (domain closure, witness form).**  A witness of D23's first-pivot `+1`
domain conditions — unit entry maximum, `A 0 0 = 1`, `(0, 0)` a complete pivot, a
real legal trace, and the actual growth ratio as the value — transports to the
transposed matrix.  In particular the normalized first-pivot domain is closed under
transposition *at the level of the actual witnesses*, which is what a downstream
reduction can call. -/
theorem firstPivot_transpose_witness {A : Matrix5} {values : List ℝ} {g : ℝ}
    (hmax : matrixEntryMax A = 1) (h00 : A 0 0 = 1)
    (hpiv : Rho5.Pivot.IsCompletePivot A 0 0)
    (htrace : Rho5.CompletePivotPath.LegalTrace A values)
    (hg : g = Rho5.GrowthModel.growthRatio A values) :
    matrixEntryMax Aᵀ = 1 ∧ Aᵀ 0 0 = 1 ∧ Rho5.Pivot.IsCompletePivot Aᵀ 0 0 ∧
      Rho5.CompletePivotPath.LegalTrace Aᵀ values ∧
        g = Rho5.GrowthModel.growthRatio Aᵀ values :=
  ⟨by rw [matrixEntryMax_transpose, hmax],
    by rw [transpose_zero_zero, h00],
    (isCompletePivot_transpose_iff A 0 0).mp hpiv,
    (legalTrace_transpose_iff).mpr htrace,
    by rw [hg, growthRatio_transpose]⟩

end Rho5.TraceTranspose
