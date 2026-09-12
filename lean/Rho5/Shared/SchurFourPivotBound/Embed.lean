import Rho5.Certificate.B24Extraction.Extract
import Rho5.ExternalFourthPivot.Main
import Rho5.ExternalTailSaturation.Basic
import Rho5.Shared.FirstPivotDomain.PivotEntry
import Rho5.Shared.LeadingTrace

/-!
# D138 / `Rho5.Shared.SchurFourPivotBound` — zero-row/column padding of a complete-pivot path

The 4x4 first Schur complement `S4 M` carries the fourth pivot `delta M = w M - t M * s M / r M`
as its **fourth** readout, while D124's fourth-readout bound is stated for `Matrix5`.  This module
supplies the bridge: embed an `n x n` matrix into the leading block of an `(n+1) x (n+1)` matrix
with a zero last row and column, and prove that

* one pivot-`(0,0)` Schur step commutes with the padding (`pivotSchur_padLast`),
* the complete-pivot property and the pivot entry are preserved
  (`isCompletePivot_padLast_iff`, `padLast_zero_zero`),
* and an all-`(0,0)` complete-pivot path lifts to the padded matrix, keeping the readouts in order
  and appending one zero readout for the padded zero `1 x 1` stop (`ZeroTrace.toLegalTrace_padLast`).

Nothing here is an abstract list: `ZeroTrace` records the real matrices, the real complete pivots
and the real Schur updates, and `toLegalTrace_padLast` produces the frozen `LegalTrace`.
-/

noncomputable section

namespace Rho5.Shared.SchurFourPivotBound

open Rho5 (Matrix5)
open Rho5.Pivot (IsCompletePivot fixedSchur)
open Rho5.PivotReindex (pivotSchur remainingIndex)
open Rho5.CompletePivotPath (LegalTrace)

/-- Embed `B : n x n` into the leading block of an `(n+1) x (n+1)` matrix, with a zero last row
and a zero last column. -/
def padLast {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => if hi : (i : ℕ) < n then (if hj : (j : ℕ) < n then B ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0

/-! ## 1. Entry readings of the padded matrix -/

theorem padLast_apply_lt {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin (n+1))
    (hi : (i : ℕ) < n) (hj : (j : ℕ) < n) : padLast B i j = B ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp only [padLast]
  rw [dif_pos hi, dif_pos hj]

theorem padLast_castSucc_castSucc {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    padLast B i.castSucc j.castSucc = B i j :=
  padLast_apply_lt B i.castSucc j.castSucc i.isLt j.isLt

/-- The padded leading entry is the original one. -/
theorem padLast_zero_zero {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    padLast B 0 0 = B 0 0 :=
  padLast_apply_lt B 0 0 (Nat.succ_pos n) (Nat.succ_pos n)

theorem padLast_last_col {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin (n+1)) :
    padLast B i (Fin.last n) = 0 := by
  simp only [padLast]
  split_ifs with h1 h2
  · exact absurd h2 (by simp [Fin.last])
  · rfl
  · rfl

theorem padLast_last_row {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (j : Fin (n+1)) :
    padLast B (Fin.last n) j = 0 := by
  simp only [padLast]
  split_ifs with h1 h2
  · exact absurd h1 (by simp [Fin.last])
  · rfl
  · rfl

/-- The `0 x 0` matrix pads to the zero `1 x 1` matrix. -/
theorem padLast_size_zero :
    padLast (0 : Matrix (Fin 0) (Fin 0) ℝ) = (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i
  exact padLast_last_row _ j

/-! ## 2. Padding commutes with one pivot-`(0,0)` Schur step -/

/-- The pivot-`(0,0)` Schur step is the frozen fixed-position update. -/
theorem pivotSchur_zero_zero {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    pivotSchur A 0 0 = fixedSchur A := by
  rw [Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]

/-- **The padding bridge.**  The added last row and column are zero and stay zero, and the pivot
entry is unchanged, so the entrywise Schur formulas of the padded and the small matrix agree. -/
theorem fixedSchur_padLast {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    fixedSchur (padLast B) = padLast (fixedSchur B) := by
  ext i j
  simp only [fixedSchur]
  rcases lt_or_eq_of_le (Nat.le_of_lt_succ i.isLt) with hi | hi
  · rcases lt_or_eq_of_le (Nat.le_of_lt_succ j.isLt) with hj | hj
    · rw [padLast_apply_lt B i.succ j.succ (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj),
        padLast_apply_lt B i.succ (0 : Fin (n+2)) (Nat.succ_lt_succ hi) (Nat.succ_pos n),
        padLast_apply_lt B (0 : Fin (n+2)) j.succ (Nat.succ_pos n) (Nat.succ_lt_succ hj),
        padLast_apply_lt B (0 : Fin (n+2)) (0 : Fin (n+2)) (Nat.succ_pos n) (Nat.succ_pos n),
        padLast_apply_lt _ i j hi hj]
      simp only [fixedSchur]
      rfl
    · have hj1 : j.succ = Fin.last (n+1) := Fin.ext (by simp [Fin.succ, Fin.last, hj])
      have hj2 : j = Fin.last n := Fin.ext (by simp [Fin.last, hj])
      rw [hj1, padLast_last_col B i.succ, padLast_last_col B 0, hj2,
        padLast_last_col (fixedSchur B) i]
      ring
  · have hi1 : i.succ = Fin.last (n+1) := Fin.ext (by simp [Fin.succ, Fin.last, hi])
    have hi2 : i = Fin.last n := Fin.ext (by simp [Fin.last, hi])
    rw [hi1, padLast_last_row B j.succ, padLast_last_row B (0 : Fin (n+2)),
      hi2, padLast_last_row (fixedSchur B) j]
    ring

theorem pivotSchur_padLast {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    pivotSchur (padLast B) 0 0 = padLast (pivotSchur B 0 0) := by
  rw [pivotSchur_zero_zero, fixedSchur_padLast, pivotSchur_zero_zero]

/-! ## 3. Complete pivots and the pivot entry survive the padding -/

theorem isCompletePivot_padLast_iff {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    IsCompletePivot (padLast B) 0 0 ↔ IsCompletePivot B 0 0 := by
  constructor
  · intro h i j
    have h1 := h i.castSucc j.castSucc
    rwa [padLast_castSucc_castSucc, padLast_zero_zero] at h1
  · intro h i j
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ i.isLt) with hi | hi
    · rcases lt_or_eq_of_le (Nat.le_of_lt_succ j.isLt) with hj | hj
      · rw [padLast_apply_lt B i j hi hj, padLast_zero_zero]
        exact h ⟨i, hi⟩ ⟨j, hj⟩
      · have hlast : j = Fin.last (n+1) := Fin.ext (by simp [Fin.last, hj])
        rw [hlast, padLast_last_col]
        simp
    · have hlast : i = Fin.last (n+1) := Fin.ext (by simp [Fin.last, hi])
      rw [hlast, padLast_last_row]
      simp

/-! ## 4. Full all-`(0,0)` paths and their padding -/

/-- A complete-pivot path that never stops early and always eliminates the active corner `(0,0)`.
`S4 M`, `S3 M`, `T2 M` and the final `1 x 1` block are exactly such a chain, so this is the shape
the first Schur complement actually has. -/
inductive ZeroTrace : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ → List ℝ → Prop where
  | nil : ZeroTrace 0 (0 : Matrix (Fin 0) (Fin 0) ℝ) []
  | step {n : ℕ} {B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
      (hmax : IsCompletePivot B 0 0) (hne : B 0 0 ≠ 0) {tail : List ℝ}
      (htail : ZeroTrace n (pivotSchur B 0 0) tail) :
      ZeroTrace (n+1) B (|B 0 0| :: tail)

/-- **The padding lift.**  An all-`(0,0)` path of `B` lifts to a frozen `LegalTrace` of the padded
matrix, with the readouts of `B` kept in order and one extra `0` readout: after the last step the
padded matrix is a zero `1 x 1` block, which the frozen relation records by `zeroStop`. -/
theorem ZeroTrace.toLegalTrace_padLast {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ}
    (h : ZeroTrace n B values) : LegalTrace (padLast B) (values ++ [0]) :=
  ZeroTrace.rec (motive := fun n B values _ => LegalTrace (padLast B) (values ++ [0]))
    (by
      show LegalTrace (padLast (0 : Matrix (Fin 0) (Fin 0) ℝ)) ([] ++ [0])
      rw [padLast_size_zero]
      exact LegalTrace.zeroStop rfl)
    (fun {n} {B} hmax hne {tail} _htail ih => by
      have hmax' : IsCompletePivot (padLast B) 0 0 := (isCompletePivot_padLast_iff B).mpr hmax
      have hne' : padLast B 0 0 ≠ 0 := by rwa [padLast_zero_zero]
      have htail' : LegalTrace (pivotSchur (padLast B) 0 0) (tail ++ [0]) := by
        rw [pivotSchur_padLast]
        exact ih
      have hstep : LegalTrace (padLast B) (|padLast B 0 0| :: (tail ++ [0])) :=
        LegalTrace.step (0 : Fin _) (0 : Fin _) hmax' hne' htail'
      rw [← List.cons_append, padLast_zero_zero] at hstep
      exact hstep)
    h

end Rho5.Shared.SchurFourPivotBound
