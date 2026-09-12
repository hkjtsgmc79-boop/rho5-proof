/-
D13 — whole-trace scaling equivalence
=====================================

**Goal 3.** Scaling the matrix by a nonzero scalar `c` scales the *whole* legal
trace by `|c|`, in both directions:

  `LegalTrace (c • A) (values.map (fun v => |c| * v)) ↔ LegalTrace A values`.

Every ingredient is reused, not rebuilt:

* the pivot qualification is transported by D08's
  `Rho5.MatrixNormalization.isCompletePivot_smul_iff` (fixed position, tied pivots
  preserved, no uniqueness used);
* the one-step update scales by D10's `Rho5.PivotReindex.pivotSchur_smul`, which
  itself rests on D08's `fixedSchur_smul`;
* the recorded value scales by `|c * A p q| = |c| * |A p q|`.

The equivalence covers all three constructors — the `0 × 0` terminal (`empty`), the
immediate zero stop (`zeroStop`), and every genuine step — and it does not assume
that any intermediate matrix is nonzero or of full rank: a trace may stop at a zero
matrix at any stage.
-/
import Rho5.Shared.CompletePivotPath.Basic
import Rho5.Shared.MatrixNormalization

namespace Rho5.CompletePivotPath

open Rho5

/-- **Goal 3 (scaling a trace up).** A legal trace of `A` scales to a legal trace of
`c • A` whose recorded values are the originals multiplied by `|c|`. -/
theorem legalTrace_smul : ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ}
    (c : ℝ), c ≠ 0 → LegalTrace A values →
      LegalTrace (c • A) (values.map (fun v => |c| * v))
  | _, _, _, c, _, .empty => by
      have h0 : (c • (0 : Matrix (Fin 0) (Fin 0) ℝ)) = 0 := by
        funext i j
        exact Fin.elim0 i
      rw [h0]
      simp only [List.map_nil]
      exact LegalTrace.empty
  | _, _, _, c, _, .zeroStop hzero => by
      rw [hzero, smul_zero]
      simp only [List.map_cons, List.map_nil, mul_zero]
      exact LegalTrace.zeroStop rfl
  | _, A, _, c, hc, .step p q hmax hne htail => by
      rw [List.map_cons]
      have hhead : |c| * |A p q| = |(c • A) p q| := by
        rw [Rho5.MatrixNormalization.smul_apply_entry, abs_mul]
      rw [hhead]
      refine LegalTrace.step p q ?_ ?_ ?_
      · exact (Rho5.MatrixNormalization.isCompletePivot_smul_iff A p q hc).mpr hmax
      · rw [Rho5.MatrixNormalization.smul_apply_entry]
        exact mul_ne_zero hc hne
      · rw [Rho5.PivotReindex.pivotSchur_smul A p q hc hne]
        exact legalTrace_smul c hc htail

/-- **Goal 3 (scaling a trace down).** A legal trace of `c • A` whose values are the
originals scaled by `|c|` comes from a legal trace of `A`.  Proved by applying the
upward direction to `c⁻¹` and cancelling, so the two directions cannot disagree. -/
theorem legalTrace_of_smul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ}
    {c : ℝ} (hc : c ≠ 0) (h : LegalTrace (c • A) (values.map (fun v => |c| * v))) :
    LegalTrace A values := by
  have h1 := legalTrace_smul c⁻¹ (inv_ne_zero hc) h
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
  have hfun : ((fun v => |c⁻¹| * v) ∘ (fun v => |c| * v)) = (id : ℝ → ℝ) := by
    funext v
    simp only [Function.comp_apply, id_eq]
    rw [← mul_assoc, abs_inv, inv_mul_cancel₀ (abs_ne_zero.mpr hc), one_mul]
  have hmap : (values.map (fun v => |c| * v)).map (fun v => |c⁻¹| * v) = values := by
    rw [List.map_map, hfun, List.map_id]
  rwa [hmap] at h1

/-- **Goal 3 (the equivalence).** Whole-trace scaling by a nonzero scalar, both
directions. -/
theorem legalTrace_smul_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (values : List ℝ)
    {c : ℝ} (hc : c ≠ 0) :
    LegalTrace (c • A) (values.map (fun v => |c| * v)) ↔ LegalTrace A values :=
  ⟨legalTrace_of_smul hc, legalTrace_smul c hc⟩

/-- **Goal 3 (negative scalar, explicit).** For `c < 0` the scaling factor is `-c`,
so negative scalars are covered without any sign assumption beyond `c < 0`. -/
theorem legalTrace_neg_smul_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (values : List ℝ)
    {c : ℝ} (hc : c < 0) :
    LegalTrace (c • A) (values.map (fun v => -c * v)) ↔ LegalTrace A values := by
  have hc0 : c ≠ 0 := ne_of_lt hc
  have habs : |c| = -c := abs_of_neg hc
  simpa only [habs] using legalTrace_smul_iff A values hc0

/-- **Goal 3 (positive scalar, explicit).** For `c > 0` the scaling factor is `c`. -/
theorem legalTrace_pos_smul_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (values : List ℝ)
    {c : ℝ} (hc : 0 < c) :
    LegalTrace (c • A) (values.map (fun v => c * v)) ↔ LegalTrace A values := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have habs : |c| = c := abs_of_pos hc
  simpa only [habs] using legalTrace_smul_iff A values hc0

/-- The inverse-scalar form, convenient when undoing a normalization step: it is the
general equivalence at `c⁻¹`, with `|c⁻¹| = |c|⁻¹`. -/
theorem legalTrace_inv_smul_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (values : List ℝ)
    {c : ℝ} (hc : c ≠ 0) :
    LegalTrace (c⁻¹ • A) (values.map (fun v => |c|⁻¹ * v)) ↔ LegalTrace A values := by
  have h := legalTrace_smul_iff A values (c := c⁻¹) (inv_ne_zero hc)
  simpa only [abs_inv] using h

end Rho5.CompletePivotPath
