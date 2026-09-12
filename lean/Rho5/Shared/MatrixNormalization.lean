/-
D08 — 矩阵元素最大范数的缩放、单位归一化与单步主元语义
=================================================================

Scope (frozen by the D08 task card).  This module supplies exactly the
normalization foundation that the global growth argument is still missing; it
does **not** claim a five-stage legal path, all row/column permutations, a
global growth-rate bound, or attainability.

Reused, unchanged, from the frozen pilot (read-only):
* `Rho5.Matrix5` and `Rho5.matrixEntryMax`  (`Rho5.Shared.Conventions`) —
  the max of the 25 entrywise absolute values, *not* an operator norm and not
  redefined here under any name;
* `Rho5.Pivot.IsCompletePivot` and `Rho5.Pivot.fixedSchur` (`Rho5.Shared.Pivot`)
  — the local complete-pivot semantics with ties permitted, and the fixed
  `(0,0)`-position Schur update.

Delivered (namespace `Rho5.MatrixNormalization`):

1. entry-max basics — `abs_entry_le_matrixEntryMax`, `matrixEntryMax_nonneg`,
   `matrixEntryMax_eq_zero_iff`, `matrixEntryMax_pos`, `matrixEntryMax_ne_zero`;
2. scaling — `smul_apply_entry` (the standard `smul` read entrywise),
   `scaledEntries` (explicit pointwise product), `scaledEntries_eq_smul`
   (it *is* the standard `smul`), `matrixEntryMax_smul`,
   `matrixEntryMax_scaledEntries`;
3. normalization — `normalize`, `normalize_eq_inv_smul`, `normalize_zero`,
   `matrixEntryMax_normalize`, `smul_normalize_eq_self`, `eq_smul_normalize`;
4. pivot scaling — `isCompletePivot_smul_iff` (any index type, so in particular
   every finite matrix), `abs_smul_entry_eq_iff` (ties preserved exactly),
   `isCompletePivot_smul_tied`, `isCompletePivot_normalize_iff`;
5. one Schur step — `fixedSchur_smul`, `fixedSchur_smul_apply`, carrying the
   explicit `c ≠ 0` and pivot `A 0 0 ≠ 0` qualifications.

No `sorry`, no new axiom, no `native_decide`; every statement is total in the
frozen definitions (division is the total real division), and the two
mathematical side conditions that make the statements *mean* what they say are
kept as explicit hypotheses.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Rho5.MatrixNormalization

open Rho5

/-! ## Auxiliary supremum facts

`matrixEntryMax` is a `Finset.sup'` over the 25 entry positions.  These
helpers record the bound and the congruence rule for such a supremum with the
argument order of the frozen mathlib API (`Finset.le_sup'` takes the function
explicitly), so that later proofs never depend on the exact spelling of the
`Nonempty` witness. -/
private theorem le_sup'_of_mem {β : Type*} (s : Finset β) (H : s.Nonempty) (f : β → ℝ) {b : β}
    (hb : b ∈ s) : f b ≤ s.sup' H f :=
  (Finset.le_sup'_iff H).mpr ⟨b, hb, le_rfl⟩

private theorem sup'_congr_fun {β : Type*} (s : Finset β) (H : s.Nonempty) {f g : β → ℝ}
    (h : ∀ b ∈ s, f b = g b) : s.sup' H f = s.sup' H g := by
  refine le_antisymm ?_ ?_
  · exact Finset.sup'_le H f (fun b hb => (h b hb).le.trans (le_sup'_of_mem s H g hb))
  · exact Finset.sup'_le H g (fun b hb => (h b hb).ge.trans (le_sup'_of_mem s H f hb))

/-- A nonnegative constant factors out of a `sup'` of real values. -/
private theorem sup'_mul_const {β : Type*} (s : Finset β) (H : s.Nonempty) (f : β → ℝ)
    {a : ℝ} (ha : 0 ≤ a) : s.sup' H (fun b => a * f b) = a * s.sup' H f := by
  refine le_antisymm ?_ ?_
  · exact Finset.sup'_le H _ (fun b hb => mul_le_mul_of_nonneg_left (le_sup'_of_mem s H f hb) ha)
  · obtain ⟨b, hb, hbmax⟩ := Finset.exists_mem_eq_sup' H f
    rw [hbmax]
    exact le_sup'_of_mem s H (fun b => a * f b) hb

/-! ## 1. Entry-max basics -/

/-- Every entry of `M`, in absolute value, is bounded by `matrixEntryMax M`.
This is the defining universal property of the 25-element maximum. -/
theorem abs_entry_le_matrixEntryMax (M : Matrix5) (i j : Fin 5) :
    |M i j| ≤ matrixEntryMax M := by
  unfold matrixEntryMax
  exact le_sup'_of_mem Finset.univ Finset.univ_nonempty
    (fun ij : Fin 5 × Fin 5 => |M ij.1 ij.2|) (Finset.mem_univ (i, j))

/-- `matrixEntryMax` is nonnegative. -/
theorem matrixEntryMax_nonneg (M : Matrix5) : 0 ≤ matrixEntryMax M :=
  le_trans (abs_nonneg (M 0 0)) (abs_entry_le_matrixEntryMax M 0 0)

/-- The entry maximum vanishes exactly on the zero matrix.  The forward
direction is where the *maximum* (rather than a mere upper bound) is used: a
vanishing maximum forces all 25 absolute values to vanish. -/
theorem matrixEntryMax_eq_zero_iff (M : Matrix5) : matrixEntryMax M = 0 ↔ M = 0 := by
  constructor
  · intro h
    funext i j
    have hle : |M i j| ≤ 0 := by
      rw [← h]
      exact abs_entry_le_matrixEntryMax M i j
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  · intro h
    rw [h]
    unfold matrixEntryMax
    exact Finset.sup'_eq_of_forall Finset.univ_nonempty
      (fun ij : Fin 5 × Fin 5 => |(0 : Matrix5) ij.1 ij.2|) (fun ij _ => by simp)

/-- A nonzero matrix has a strictly positive entry maximum.  This is the
positivity fact that makes `(matrixEntryMax M)⁻¹` a legitimate normalizer. -/
theorem matrixEntryMax_pos (M : Matrix5) (hM : M ≠ 0) : 0 < matrixEntryMax M :=
  lt_of_le_of_ne (matrixEntryMax_nonneg M)
    (fun h0 => hM ((matrixEntryMax_eq_zero_iff M).mp h0.symm))

/-- Nonzero matrix, nonzero maximum (the form used to invert it). -/
theorem matrixEntryMax_ne_zero (M : Matrix5) (hM : M ≠ 0) : matrixEntryMax M ≠ 0 :=
  ne_of_gt (matrixEntryMax_pos M hM)

/-! ## 2. Scaling the entry maximum -/

/-- The standard scalar multiplication of matrices, read entrywise.  This is
the bridge between the abstract `smul` and the explicit pointwise product used
in the next definitions. -/
theorem smul_apply_entry {ι κ : Type*} (c : ℝ) (A : Matrix ι κ ℝ) (i : ι) (j : κ) :
    (c • A) i j = c * A i j := by
  rw [Matrix.smul_apply, smul_eq_mul]

/-- Explicit pointwise scalar multiplication of the 25 entries.  It is provided
only so that the entrywise reading of the next theorem is available; the
mathematical object is the standard `smul` on matrices, as
`scaledEntries_eq_smul` records. -/
def scaledEntries (c : ℝ) (M : Matrix5) : Matrix5 := fun i j => c * M i j

/-- The explicit pointwise product coincides with the standard scalar
multiplication of matrices, entry by entry. -/
theorem scaledEntries_eq_smul (c : ℝ) (M : Matrix5) : scaledEntries c M = c • M := by
  funext i j
  simp only [scaledEntries, smul_apply_entry]

/-- **Item 2.** The entry maximum of a scalar multiple factors as the absolute
value of the scalar times the entry maximum.  No nonnegativity hypothesis on
`c` is needed: `|c|` handles the sign, and `c = 0` is covered by
`matrixEntryMax_eq_zero_iff`. -/
theorem matrixEntryMax_smul (c : ℝ) (M : Matrix5) :
    matrixEntryMax (c • M) = |c| * matrixEntryMax M := by
  unfold matrixEntryMax
  rw [sup'_congr_fun Finset.univ Finset.univ_nonempty
    (f := fun ij : Fin 5 × Fin 5 => |(c • M) ij.1 ij.2|)
    (g := fun ij : Fin 5 × Fin 5 => |c| * |M ij.1 ij.2|)
    (fun ij _ => by simp only [smul_apply_entry, abs_mul])]
  exact sup'_mul_const Finset.univ Finset.univ_nonempty
    (fun ij : Fin 5 × Fin 5 => |M ij.1 ij.2|) (abs_nonneg c)

/-- The same statement read on the explicit pointwise product. -/
theorem matrixEntryMax_scaledEntries (c : ℝ) (M : Matrix5) :
    matrixEntryMax (scaledEntries c M) = |c| * matrixEntryMax M := by
  rw [scaledEntries_eq_smul, matrixEntryMax_smul]

/-! ## 3. Unit normalization -/

/-- Normalize by the reciprocal of the entry maximum.  For the zero matrix this
is the zero matrix (total real inverse); for every nonzero matrix it is the
multiple of `M` whose entry maximum is `1`. -/
noncomputable def normalize (M : Matrix5) : Matrix5 := (matrixEntryMax M)⁻¹ • M

/-- Defining equation of `normalize`, kept for rewriting. -/
theorem normalize_eq_inv_smul (M : Matrix5) :
    normalize M = (matrixEntryMax M)⁻¹ • M := rfl

/-- The zero matrix normalizes to the zero matrix. -/
theorem normalize_zero : normalize 0 = 0 := by
  simp [normalize]

/-- **Item 3 (unit maximum).** Every nonzero matrix normalizes to entry maximum
exactly `1`. -/
theorem matrixEntryMax_normalize (M : Matrix5) (hM : M ≠ 0) :
    matrixEntryMax (normalize M) = 1 := by
  rw [normalize_eq_inv_smul, matrixEntryMax_smul, abs_inv,
    abs_of_pos (matrixEntryMax_pos M hM), inv_mul_cancel₀ (matrixEntryMax_ne_zero M hM)]

/-- **Item 3 (exact restoration).** Multiplying the normalization by the entry
maximum returns `M` exactly.  The `M ≠ 0` hypothesis is what makes the scalar
invertible; for `M = 0` the normalizer `(matrixEntryMax 0)⁻¹` is `0`, so the
restoration identity would assert `0 = M`. -/
theorem smul_normalize_eq_self (M : Matrix5) (hM : M ≠ 0) :
    matrixEntryMax M • normalize M = M := by
  rw [normalize_eq_inv_smul, smul_smul, mul_inv_cancel₀ (matrixEntryMax_ne_zero M hM), one_smul]

/-- The restoration identity in the orientation `M = max(M) • normalize M`. -/
theorem eq_smul_normalize (M : Matrix5) (hM : M ≠ 0) :
    M = matrixEntryMax M • normalize M :=
  (smul_normalize_eq_self M hM).symm

/-! ## 4. Scalar multiples and complete pivots -/

/-- **Item 4.** For a nonzero scalar, multiplication by `c` is an equivalence
for the complete-pivot property at a *fixed* position.  The index types are
arbitrary, so this covers every finite matrix; no uniqueness of the maximizer is
used or implied, hence tied pivots are preserved.  This reuses
`Rho5.Pivot.IsCompletePivot` unchanged. -/
theorem isCompletePivot_smul_iff {ι κ : Type*} (A : Matrix ι κ ℝ) (p : ι) (q : κ)
    {c : ℝ} (hc : c ≠ 0) :
    Rho5.Pivot.IsCompletePivot (c • A) p q ↔ Rho5.Pivot.IsCompletePivot A p q := by
  have hcabs : 0 < |c| := abs_pos.mpr hc
  constructor
  · intro h i j
    have h' : |c| * |A i j| ≤ |c| * |A p q| := by
      simpa only [smul_apply_entry, abs_mul] using h i j
    exact le_of_mul_le_mul_left h' hcabs
  · intro h i j
    simp only [smul_apply_entry, abs_mul]
    exact mul_le_mul_of_nonneg_left (h i j) (le_of_lt hcabs)

/-- Tie preservation, explicitly: two positions are tied for the maximum before
scaling exactly when they are tied after scaling by a nonzero scalar. -/
theorem abs_smul_entry_eq_iff {ι κ : Type*} (A : Matrix ι κ ℝ) (p p' : ι) (q q' : κ)
    {c : ℝ} (hc : c ≠ 0) :
    |(c • A) p' q'| = |(c • A) p q| ↔ |A p' q'| = |A p q| := by
  have hcabs : 0 < |c| := abs_pos.mpr hc
  constructor
  · intro h
    have h' : |c| * |A p' q'| = |c| * |A p q| := by
      simpa only [smul_apply_entry, abs_mul] using h
    exact mul_left_cancel₀ (ne_of_gt hcabs) h'
  · intro h
    simp only [smul_apply_entry, abs_mul, h]

/-- A tied maximizer of `A` stays a legal complete pivot of `c • A` for every
`c ≠ 0`; this is `Rho5.Pivot.tied_pivot` transported across the scaling
equivalence. -/
theorem isCompletePivot_smul_tied {ι κ : Type*} (A : Matrix ι κ ℝ) (p p' : ι) (q q' : κ)
    {c : ℝ} (hc : c ≠ 0) (hmax : Rho5.Pivot.IsCompletePivot A p q)
    (htie : |A p' q'| = |A p q|) :
    Rho5.Pivot.IsCompletePivot (c • A) p' q' :=
  Rho5.Pivot.tied_pivot (c • A) p p' q q'
    ((isCompletePivot_smul_iff A p q hc).mpr hmax)
    ((abs_smul_entry_eq_iff A p p' q q' hc).mpr htie)

/-- Derived interface: for a nonzero matrix, normalizing does not change which
positions are complete pivots (apply item 4 to the nonzero scalar
`(matrixEntryMax M)⁻¹`, which item 3 makes invertible). -/
theorem isCompletePivot_normalize_iff (M : Matrix5) (hM : M ≠ 0) (p q : Fin 5) :
    Rho5.Pivot.IsCompletePivot (normalize M) p q ↔ Rho5.Pivot.IsCompletePivot M p q := by
  rw [normalize_eq_inv_smul]
  exact isCompletePivot_smul_iff M p q (inv_ne_zero (matrixEntryMax_ne_zero M hM))

/-! ## 5. One fixed-position Schur step under scaling -/

/-- **Item 5.** Scaling a `(n+1) × (n+1)` matrix by a nonzero scalar scales its
fixed-position Schur update by the same scalar, *provided the pivot `A 0 0` is
nonzero*.  The pivot condition is the qualification that makes `fixedSchur` the
Schur complement of a legitimate elimination step; it is kept as an explicit
hypothesis (the total real division would silently return `0` at a vanishing
pivot, which is an artifact of the encoding, not a mathematical case). -/
theorem fixedSchur_smul {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) {c : ℝ}
    (hc : c ≠ 0) (hA : A 0 0 ≠ 0) :
    Rho5.Pivot.fixedSchur (c • A) = c • Rho5.Pivot.fixedSchur A := by
  ext i j
  have hcA : c * A 0 0 ≠ 0 := mul_ne_zero hc hA
  simp only [Rho5.Pivot.fixedSchur, smul_apply_entry]
  -- `field_simp` clears the two denominators `A 0 0` and `c * A 0 0` (legitimate
  -- by `hA` and `hcA`) and then closes the resulting polynomial identity.
  field_simp

/-- Pointwise form of the one-step scaling law. -/
theorem fixedSchur_smul_apply {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) {c : ℝ}
    (hc : c ≠ 0) (hA : A 0 0 ≠ 0) (i j : Fin n) :
    Rho5.Pivot.fixedSchur (c • A) i j = c * Rho5.Pivot.fixedSchur A i j := by
  rw [fixedSchur_smul A hc hA, smul_apply_entry]

end Rho5.MatrixNormalization
