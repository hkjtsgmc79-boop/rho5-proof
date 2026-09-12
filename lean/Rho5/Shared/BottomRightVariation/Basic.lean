import Rho5.Certificate.B24Extraction
import Rho5.Shared.CanonicalTail
import Rho5.Shared.MatrixNormalization
import Rho5.Shared.TailEnvelope
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# D55 — legal bottom-right variation of the actual `5 × 5` matrix

The card fixes one variation of the actual whole matrix of the B24 lane: only the
original entry `(4,4)` moves, to `M 4 4 + h`.  This file defines that variation
(`shift`) and proves the *real* Schur bookkeeping behind it, using the actual D37
readings `S4/S3/T2/p/k/r/s/t` (each of which is the frozen D10 `pivotSchur` at the
active corner) and the actual D48 tail coordinate `delta`.

Because only `(4,4)` moves, the three successive Schur updates move exactly one
diagonal entry each:

* `S4` changes only at `(3,3)`: `S4 (shift M h) 3 3 = S4 M 3 3 + h`;
* `S3` changes only at `(2,2)`: `S3 (shift M h) 2 2 = S3 M 2 2 + h`;
* `T2` changes only at `(1,1)`: `T2 (shift M h) 1 1 = T2 M 1 1 + h`.

Consequently the leading readings `p k r s t` are unchanged, the tail coordinate
`d = T2 · 1 1` moves to `d + h`, and (for the actual `delta` of D48) `delta` moves to
`delta + h`.  Nothing here is a generic perturbation framework: every statement is an
entrywise computation on the fixed `5 → 4 → 3 → 2` chain, and no hypothesis about the
matrix beyond the explicitly named readings is used.
-/

namespace Rho5.BottomRightVariation

open Rho5 (Matrix5 matrixEntryMax)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)

/-! ## 1. The corner shift -/

/-- **The variation.**  `shift M h` is `M` with the original entry `(4,4)` changed to
`M 4 4 + h`; every other entry is literally the same. -/
def shift (M : Matrix5) (h : ℝ) : Matrix5 :=
  fun i j => if i = 4 ∧ j = 4 then M i j + h else M i j

/-- Defining equation of `shift`, kept for rewriting. -/
theorem shift_apply (M : Matrix5) (h : ℝ) (i j : Fin 5) :
    shift M h i j = if i = 4 ∧ j = 4 then M i j + h else M i j := rfl

/-- The varied entry itself. -/
@[simp] theorem shift_self (M : Matrix5) (h : ℝ) : shift M h 4 4 = M 4 4 + h := by
  rw [shift_apply, if_pos (by decide)]

/-- Any entry other than `(4,4)` is untouched. -/
theorem shift_of_ne (M : Matrix5) (h : ℝ) {i j : Fin 5} (hij : ¬ (i = 4 ∧ j = 4)) :
    shift M h i j = M i j := by
  rw [shift_apply, if_neg hij]

/-- Untouched because the row is not the last one. -/
@[simp] theorem shift_of_ne_left (M : Matrix5) (h : ℝ) {i j : Fin 5} (hi : i ≠ 4) :
    shift M h i j = M i j :=
  shift_of_ne M h (fun hij => hi hij.1)

/-- Untouched because the column is not the last one. -/
@[simp] theorem shift_of_ne_right (M : Matrix5) (h : ℝ) {i j : Fin 5} (hj : j ≠ 4) :
    shift M h i j = M i j :=
  shift_of_ne M h (fun hij => hj hij.2)

/-- The zero variation is the identity. -/
theorem shift_zero (M : Matrix5) : shift M 0 = M := by
  funext i j
  by_cases hij : i = 4 ∧ j = 4
  · rw [shift_apply, if_pos hij, add_zero]
  · rw [shift_apply, if_neg hij]

/-! ## 2. The first Schur update `S4`: only `(3,3)` moves -/

/-- **`S4`, moved corner.**  The first Schur update of the varied matrix differs from
that of `M` exactly by `h` at `(3,3)`. -/
theorem S4_shift_33 (M : Matrix5) (h : ℝ) : S4 (shift M h) 3 3 = S4 M 3 3 + h := by
  have h1 : S4 (shift M h) 3 3
      = shift M h 4 4 - shift M h 4 0 * shift M h 0 4 / shift M h 0 0 :=
    Rho5.Certificate.B24Extraction.S4_apply (shift M h) 3 3
  have h2 : S4 M 3 3 = M 4 4 - M 4 0 * M 0 4 / M 0 0 := Rho5.Certificate.B24Extraction.S4_apply M 3 3
  rw [h1, h2, shift_self,
    shift_of_ne_right (M := M) (h := h) (i := (4 : Fin 5)) (j := (0 : Fin 5)) (by decide),
    shift_of_ne_left (M := M) (h := h) (i := (0 : Fin 5)) (j := (4 : Fin 5)) (by decide),
    shift_of_ne_left (M := M) (h := h) (i := (0 : Fin 5)) (j := (0 : Fin 5)) (by decide)]
  ring

/-- **`S4`, away from the corner.**  Every other entry of the first Schur update is
unchanged. -/
theorem S4_shift_of_ne (M : Matrix5) (h : ℝ) {i j : Fin 4} (hij : ¬ (i = 3 ∧ j = 3)) :
    S4 (shift M h) i j = S4 M i j := by
  have hsucc : ¬ ((i.succ : Fin 5) = 4 ∧ (j.succ : Fin 5) = 4) := by
    rintro ⟨e1, e2⟩
    exact hij ⟨Fin.succ_inj.mp e1, Fin.succ_inj.mp e2⟩
  rw [Rho5.Certificate.B24Extraction.S4_apply (shift M h) i j, Rho5.Certificate.B24Extraction.S4_apply M i j, shift_of_ne M h hsucc,
    shift_of_ne_right (M := M) (h := h) (i := i.succ) (j := (0 : Fin 5)) (by decide),
    shift_of_ne_left (M := M) (h := h) (i := (0 : Fin 5)) (j := j.succ) (by decide),
    shift_of_ne_left (M := M) (h := h) (i := (0 : Fin 5)) (j := (0 : Fin 5)) (by decide)]

/-- The same two facts in a single `if`-form, convenient for case bashes. -/
theorem S4_shift_apply (M : Matrix5) (h : ℝ) (i j : Fin 4) :
    S4 (shift M h) i j = if i = 3 ∧ j = 3 then S4 M i j + h else S4 M i j := by
  by_cases hij : i = 3 ∧ j = 3
  · obtain ⟨rfl, rfl⟩ := hij
    rw [if_pos ⟨rfl, rfl⟩, S4_shift_33]
  · rw [if_neg hij, S4_shift_of_ne M h hij]

/-- The `(0,0)` corner of `S4`, i.e. the second pivot reading. -/
theorem S4_shift_00 (M : Matrix5) (h : ℝ) : S4 (shift M h) 0 0 = S4 M 0 0 :=
  S4_shift_of_ne M h (by decide)

/-! ## 3. The second Schur update `S3`: only `(2,2)` moves -/

/-- **`S3`, moved corner.**  The second Schur update gains exactly `h` at `(2,2)`. -/
theorem S3_shift_22 (M : Matrix5) (h : ℝ) : S3 (shift M h) 2 2 = S3 M 2 2 + h := by
  have h1 : S3 (shift M h) 2 2
      = S4 (shift M h) 3 3 - S4 (shift M h) 3 0 * S4 (shift M h) 0 3 / S4 (shift M h) 0 0 :=
    Rho5.Certificate.B24Extraction.S3_apply (shift M h) 2 2
  have h2 : S3 M 2 2 = S4 M 3 3 - S4 M 3 0 * S4 M 0 3 / S4 M 0 0 := Rho5.Certificate.B24Extraction.S3_apply M 2 2
  rw [h1, h2, S4_shift_33,
    S4_shift_of_ne (M := M) (h := h) (i := (3 : Fin 4)) (j := (0 : Fin 4)) (by decide),
    S4_shift_of_ne (M := M) (h := h) (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide),
    S4_shift_of_ne (M := M) (h := h) (i := (0 : Fin 4)) (j := (0 : Fin 4)) (by decide)]
  ring

/-- **`S3`, away from the corner.** -/
theorem S3_shift_of_ne (M : Matrix5) (h : ℝ) {i j : Fin 3} (hij : ¬ (i = 2 ∧ j = 2)) :
    S3 (shift M h) i j = S3 M i j := by
  have h1 : ¬ ((i.succ : Fin 4) = 3 ∧ (j.succ : Fin 4) = 3) := by
    rintro ⟨e1, e2⟩
    exact hij ⟨Fin.succ_inj.mp e1, Fin.succ_inj.mp e2⟩
  have h2 : ¬ ((i.succ : Fin 4) = 3 ∧ (0 : Fin 4) = 3) := fun hc => absurd hc.2 (by decide)
  have h3 : ¬ ((0 : Fin 4) = 3 ∧ (j.succ : Fin 4) = 3) := fun hc => absurd hc.1 (by decide)
  have h4 : ¬ ((0 : Fin 4) = 3 ∧ (0 : Fin 4) = 3) := fun hc => absurd hc.1 (by decide)
  rw [Rho5.Certificate.B24Extraction.S3_apply (shift M h) i j, Rho5.Certificate.B24Extraction.S3_apply M i j, S4_shift_of_ne M h h1,
    S4_shift_of_ne M h h2, S4_shift_of_ne M h h3, S4_shift_of_ne M h h4]

/-- The same two facts in a single `if`-form. -/
theorem S3_shift_apply (M : Matrix5) (h : ℝ) (i j : Fin 3) :
    S3 (shift M h) i j = if i = 2 ∧ j = 2 then S3 M i j + h else S3 M i j := by
  by_cases hij : i = 2 ∧ j = 2
  · obtain ⟨rfl, rfl⟩ := hij
    rw [if_pos ⟨rfl, rfl⟩, S3_shift_22]
  · rw [if_neg hij, S3_shift_of_ne M h hij]

/-- The `(0,0)` corner of `S3`, i.e. the third pivot reading. -/
theorem S3_shift_00 (M : Matrix5) (h : ℝ) : S3 (shift M h) 0 0 = S3 M 0 0 :=
  S3_shift_of_ne M h (by decide)

/-! ## 4. The third Schur update `T2`: only `(1,1)` moves -/

/-- **`T2`, moved corner.**  The `2 × 2` tail gains exactly `h` at `(1,1)`. -/
theorem T2_shift_11 (M : Matrix5) (h : ℝ) : T2 (shift M h) 1 1 = T2 M 1 1 + h := by
  have h1 : T2 (shift M h) 1 1
      = S3 (shift M h) 2 2 - S3 (shift M h) 2 0 * S3 (shift M h) 0 2 / S3 (shift M h) 0 0 :=
    Rho5.Certificate.B24Extraction.T2_apply (shift M h) 1 1
  have h2 : T2 M 1 1 = S3 M 2 2 - S3 M 2 0 * S3 M 0 2 / S3 M 0 0 := Rho5.Certificate.B24Extraction.T2_apply M 1 1
  rw [h1, h2, S3_shift_22,
    S3_shift_of_ne (M := M) (h := h) (i := (2 : Fin 3)) (j := (0 : Fin 3)) (by decide),
    S3_shift_of_ne (M := M) (h := h) (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide),
    S3_shift_of_ne (M := M) (h := h) (i := (0 : Fin 3)) (j := (0 : Fin 3)) (by decide)]
  ring

/-- **`T2`, away from the corner.** -/
theorem T2_shift_of_ne (M : Matrix5) (h : ℝ) {i j : Fin 2} (hij : ¬ (i = 1 ∧ j = 1)) :
    T2 (shift M h) i j = T2 M i j := by
  have h1 : ¬ ((i.succ : Fin 3) = 2 ∧ (j.succ : Fin 3) = 2) := by
    rintro ⟨e1, e2⟩
    exact hij ⟨Fin.succ_inj.mp e1, Fin.succ_inj.mp e2⟩
  have h2 : ¬ ((i.succ : Fin 3) = 2 ∧ (0 : Fin 3) = 2) := fun hc => absurd hc.2 (by decide)
  have h3 : ¬ ((0 : Fin 3) = 2 ∧ (j.succ : Fin 3) = 2) := fun hc => absurd hc.1 (by decide)
  have h4 : ¬ ((0 : Fin 3) = 2 ∧ (0 : Fin 3) = 2) := fun hc => absurd hc.1 (by decide)
  rw [Rho5.Certificate.B24Extraction.T2_apply (shift M h) i j, Rho5.Certificate.B24Extraction.T2_apply M i j, S3_shift_of_ne M h h1,
    S3_shift_of_ne M h h2, S3_shift_of_ne M h h3, S3_shift_of_ne M h h4]

/-- The same two facts in a single `if`-form. -/
theorem T2_shift_apply (M : Matrix5) (h : ℝ) (i j : Fin 2) :
    T2 (shift M h) i j = if i = 1 ∧ j = 1 then T2 M i j + h else T2 M i j := by
  by_cases hij : i = 1 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := hij
    rw [if_pos ⟨rfl, rfl⟩, T2_shift_11]
  · rw [if_neg hij, T2_shift_of_ne M h hij]

/-- The `(0,0)` corner of `T2`, i.e. the fourth pivot reading. -/
theorem T2_shift_00 (M : Matrix5) (h : ℝ) : T2 (shift M h) 0 0 = T2 M 0 0 :=
  T2_shift_of_ne M h (by decide)

/-! ## 5. The actual readings of D37 and D48 after the shift -/

/-- The second pivot reading is unchanged. -/
theorem p_shift (M : Matrix5) (h : ℝ) : p (shift M h) = p M := by
  rw [p, p]
  exact S4_shift_00 M h

/-- The third pivot reading is unchanged. -/
theorem k_shift (M : Matrix5) (h : ℝ) : k (shift M h) = k M := by
  rw [k, k]
  exact S3_shift_00 M h

/-- The tail pivot reading is unchanged. -/
theorem r_shift (M : Matrix5) (h : ℝ) : r (shift M h) = r M := by
  rw [r, r]
  exact T2_shift_00 M h

/-- The tail entry `(0,1)` is unchanged. -/
theorem s_shift (M : Matrix5) (h : ℝ) : s (shift M h) = s M := by
  rw [s, s]
  exact T2_shift_of_ne M h (by decide)

/-- The tail entry `(1,0)` is unchanged. -/
theorem t_shift (M : Matrix5) (h : ℝ) : t (shift M h) = t M := by
  rw [t, t]
  exact T2_shift_of_ne M h (by decide)

/-- The tail entry `d = T2 · 1 1` moves to `d + h`. -/
noncomputable def d (M : Matrix5) : ℝ := T2 M 1 1

/-- The moved `d`. -/
theorem d_shift (M : Matrix5) (h : ℝ) : d (shift M h) = d M + h := by
  rw [d, d, T2_shift_11]

/-- **The D48 tail coordinate `delta` moves to `delta + h`.**  The denominator `r` is
literally the same on both sides, so no nonvanishing hypothesis is needed. -/
theorem delta_shift (M : Matrix5) (h : ℝ) :
    Rho5.CanonicalTail.delta (shift M h) = Rho5.CanonicalTail.delta M + h := by
  rw [Rho5.CanonicalTail.delta, Rho5.CanonicalTail.delta, T2_shift_11, t_shift, s_shift,
    r_shift]
  ring

end Rho5.BottomRightVariation
