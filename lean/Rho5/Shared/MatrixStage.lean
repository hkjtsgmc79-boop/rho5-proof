/-
D12 — 各阶矩阵的最大条目与合法主元存在
=========================================

Purpose (frozen by the D12 task card): supply, for every nonempty stage size
`n + 1 ≥ 1`, the entrywise absolute-value maximum and the finite existence of a
legal complete pivot, together with the bridge to the frozen 5×5 semantics.

Scope: only the finite maximum / pivot-existence interface.  This module does
**not** prove a full elimination path, does not do row/column reindexing (D10),
one-step growth (D11), matrix attainability, or an optimal global bound; it
introduces no general-purpose finite-lattice library and no operator norm.

Reused unchanged from the frozen inputs (read-only):
* `Rho5.Matrix5`, `Rho5.matrixEntryMax` (`Rho5.Shared.Conventions`);
* `Rho5.Pivot.IsCompletePivot`, `Rho5.Pivot.zero_complete_pivot`
  (`Rho5.Shared.Pivot`);
* `Rho5.MatrixNormalization.smul_apply_entry`
  (`Rho5.Shared.MatrixNormalization`, D08).

Delivered (namespace `Rho5.MatrixStage`):

1. `stageEntryMax` — the nonempty finite maximum of the entrywise absolute
   values of an `(n+1) × (n+1)` real matrix, with
   `stageEntryMax_eq_matrixEntryMax` proving that at `n = 4` it *is*
   `Rho5.matrixEntryMax` (no second, incompatible 5×5 norm);
2. `stageEntryMax_nonneg`, `abs_entry_le_stageEntryMax`,
   `stageEntryMax_eq_zero_iff`, `stageEntryMax_pos`,
   `exists_abs_entry_eq_stageEntryMax` (the maximum is attained);
3. `isCompletePivot_iff_abs_eq_stageEntryMax`, `exists_completePivot`,
   `exists_nonzero_completePivot`, `completePivot_ne_zero` — every nonempty
   stage has a legal complete pivot, ties are fully allowed, and every legal
   pivot of a nonzero matrix is nonzero;
4. `stageEntryMax_smul` (any real scalar, including `0`) and
   `stageEntryMax_one` (the 1×1 stage is exactly `|A 0 0|`).

No `sorry`, no new axiom.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixNormalization
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Field.Basic

namespace Rho5.MatrixStage

open Rho5

/-! ## Auxiliary supremum facts (short, self-contained) -/

private theorem le_sup'_of_mem {β : Type*} (s : Finset β) (H : s.Nonempty) (f : β → ℝ) {b : β}
    (hb : b ∈ s) : f b ≤ s.sup' H f :=
  (Finset.le_sup'_iff H).mpr ⟨b, hb, le_rfl⟩

private theorem sup'_congr_fun {β : Type*} (s : Finset β) (H : s.Nonempty) {f g : β → ℝ}
    (h : ∀ b ∈ s, f b = g b) : s.sup' H f = s.sup' H g := by
  refine le_antisymm ?_ ?_
  · exact Finset.sup'_le H f (fun b hb => (h b hb).le.trans (le_sup'_of_mem s H g hb))
  · exact Finset.sup'_le H g (fun b hb => (h b hb).ge.trans (le_sup'_of_mem s H f hb))

private theorem sup'_mul_const {β : Type*} (s : Finset β) (H : s.Nonempty) (f : β → ℝ)
    {a : ℝ} (ha : 0 ≤ a) : s.sup' H (fun b => a * f b) = a * s.sup' H f := by
  refine le_antisymm ?_ ?_
  · exact Finset.sup'_le H _ (fun b hb => mul_le_mul_of_nonneg_left (le_sup'_of_mem s H f hb) ha)
  · obtain ⟨b, hb, hbmax⟩ := Finset.exists_mem_eq_sup' H f
    rw [hbmax]
    exact le_sup'_of_mem s H (fun b => a * f b) hb

/-! ## 1. The stage entry maximum -/

/-- Entrywise absolute-value maximum of an `(n+1) × (n+1)` real matrix: the
finite `sup'` over the `(n+1)²` entry positions (which are nonempty for every
`n`).  This extends the frozen 5×5 `matrixEntryMax` to every nonempty stage
size; item 1 of the card requires them to agree at `n = 4`. -/
noncomputable def stageEntryMax {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun ij : Fin (n + 1) × Fin (n + 1) => |A ij.1 ij.2|)

/-- **Item 1 (bridge).** At `n = 4` the stage maximum *is* the frozen
`Rho5.matrixEntryMax`; no second, incompatible 5×5 norm is introduced. -/
theorem stageEntryMax_eq_matrixEntryMax (A : Matrix5) :
    stageEntryMax A = matrixEntryMax A := rfl

/-! ## 2. Elementary properties and attainment -/

/-- Every entry, in absolute value, is bounded by the stage maximum. -/
theorem abs_entry_le_stageEntryMax {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i j : Fin (n + 1)) : |A i j| ≤ stageEntryMax A := by
  unfold stageEntryMax
  exact le_sup'_of_mem Finset.univ Finset.univ_nonempty
    (fun ij : Fin (n + 1) × Fin (n + 1) => |A ij.1 ij.2|) (Finset.mem_univ (i, j))

/-- The stage maximum is nonnegative. -/
theorem stageEntryMax_nonneg {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    0 ≤ stageEntryMax A :=
  le_trans (abs_nonneg (A 0 0)) (abs_entry_le_stageEntryMax A 0 0)

/-- The stage maximum vanishes exactly on the zero matrix. -/
theorem stageEntryMax_eq_zero_iff {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    stageEntryMax A = 0 ↔ A = 0 := by
  constructor
  · intro h
    funext i j
    have hle : |A i j| ≤ 0 := by
      rw [← h]
      exact abs_entry_le_stageEntryMax A i j
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  · intro h
    rw [h]
    unfold stageEntryMax
    exact Finset.sup'_eq_of_forall Finset.univ_nonempty
      (fun ij : Fin (n + 1) × Fin (n + 1) => |(0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) ij.1 ij.2|)
      (fun ij _ => by simp)

/-- A nonzero matrix has a strictly positive stage maximum. -/
theorem stageEntryMax_pos {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A ≠ 0) : 0 < stageEntryMax A :=
  lt_of_le_of_ne (stageEntryMax_nonneg A)
    (fun h0 => hA ((stageEntryMax_eq_zero_iff A).mp h0.symm))

/-- **Item 2 (attainment).** The stage maximum is attained at an actual entry. -/
theorem exists_abs_entry_eq_stageEntryMax {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ∃ p q, |A p q| = stageEntryMax A := by
  unfold stageEntryMax
  obtain ⟨ij, _, hij⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun ij : Fin (n + 1) × Fin (n + 1) => |A ij.1 ij.2|)
  exact ⟨ij.1, ij.2, hij.symm⟩

/-! ## 3. Complete pivots exist at every nonempty stage -/

/-- **Item 3 (equivalence).** A position is a legal complete pivot exactly when
its entry attains the stage maximum.  No uniqueness or tie-break rule is
involved: all tied maximizers are legal. -/
theorem isCompletePivot_iff_abs_eq_stageEntryMax {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p : Fin (n + 1)) (q : Fin (n + 1)) :
    Rho5.Pivot.IsCompletePivot A p q ↔ |A p q| = stageEntryMax A := by
  constructor
  · intro h
    unfold stageEntryMax
    exact le_antisymm
      (le_sup'_of_mem Finset.univ Finset.univ_nonempty
        (fun ij : Fin (n + 1) × Fin (n + 1) => |A ij.1 ij.2|) (Finset.mem_univ (p, q)))
      (Finset.sup'_le Finset.univ_nonempty
        (fun ij : Fin (n + 1) × Fin (n + 1) => |A ij.1 ij.2|)
        (fun ij _ => h ij.1 ij.2))
  · intro h i j
    rw [h]
    exact abs_entry_le_stageEntryMax A i j

/-- **Item 3 (existence).** Every nonempty stage has a legal complete pivot. -/
theorem exists_completePivot {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ∃ p q, Rho5.Pivot.IsCompletePivot A p q := by
  obtain ⟨p, q, hpq⟩ := exists_abs_entry_eq_stageEntryMax A
  exact ⟨p, q, (isCompletePivot_iff_abs_eq_stageEntryMax A p q).mpr hpq⟩

/-- Any legal complete pivot of a nonzero matrix is nonzero (its absolute value
is the strictly positive stage maximum). -/
theorem completePivot_ne_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A ≠ 0) (p : Fin (n + 1)) (q : Fin (n + 1))
    (hpq : Rho5.Pivot.IsCompletePivot A p q) : A p q ≠ 0 := by
  intro h0
  exact hA (funext fun i => funext fun j => Rho5.Pivot.zero_complete_pivot A p q hpq h0 i j)

/-- **Item 3 (nonzero pivot).** A nonzero matrix has a legal complete pivot with
nonzero pivot value. -/
theorem exists_nonzero_completePivot {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A ≠ 0) :
    ∃ p q, Rho5.Pivot.IsCompletePivot A p q ∧ A p q ≠ 0 := by
  obtain ⟨p, q, hpq⟩ := exists_completePivot A
  exact ⟨p, q, hpq, completePivot_ne_zero A hA p q hpq⟩

/-! ## 4. Scaling and the 1×1 stage -/

/-- **Item 4 (scaling).** The stage maximum scales by the absolute value of the
scalar, for every real `c` — including `c = 0` (both sides are then `0`, since
`0 • A = 0`). -/
theorem stageEntryMax_smul {n : ℕ} (c : ℝ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    stageEntryMax (c • A) = |c| * stageEntryMax A := by
  unfold stageEntryMax
  rw [sup'_congr_fun Finset.univ Finset.univ_nonempty
    (f := fun ij : Fin (n + 1) × Fin (n + 1) => |(c • A) ij.1 ij.2|)
    (g := fun ij : Fin (n + 1) × Fin (n + 1) => |c| * |A ij.1 ij.2|)
    (fun ij _ => by
      simp only [Rho5.MatrixNormalization.smul_apply_entry, abs_mul])]
  exact sup'_mul_const _ _ _ (abs_nonneg c)

/-- **Item 4 (1×1 stage).** For a 1×1 matrix the stage maximum is exactly the
absolute value of its single entry — the direct interface for the last
elimination stage. -/
theorem stageEntryMax_one (A : Matrix (Fin 1) (Fin 1) ℝ) :
    stageEntryMax A = |A 0 0| := by
  unfold stageEntryMax
  refine Finset.sup'_eq_of_forall Finset.univ_nonempty
    (fun ij : Fin 1 × Fin 1 => |A ij.1 ij.2|) (fun ij _ => ?_)
  obtain ⟨i, j⟩ := ij
  have hi : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
  have hj : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt)
  rw [hi, hj]

end Rho5.MatrixStage
