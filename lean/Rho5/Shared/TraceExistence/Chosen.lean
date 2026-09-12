/-
D14 — the noncomputable chosen trace and its specifications
==========================================================

**Item 3.** From the proved existence, a trace is *chosen* by `Classical.choose`.
This is a choice function, not an algorithm: it has no computation rule, and the
module documents it as such.  The specifications below are exactly the ones later
stages consume:

* `chosenTrace_spec` — the chosen list really is a legal trace;
* `chosenTrace_length_le` — at most `n` stages;
* `chosenTrace_eq_nil_of_order_zero` — at order `0` the chosen trace is `[]`
  (the terminal stage adds no extra `0`);
* `chosenTrace_zero_eq_singleton` — at a positive-order zero matrix it is `[0]`;
* `chosenTrace_ne_nil` — at positive order it is nonempty;
* `chosenTrace_nonneg` — every recorded value is nonnegative;
* `chosenTrace5_head` — for a nonzero `5 × 5` matrix the chosen trace is nonempty and
  its head is the frozen entry maximum `Rho5.matrixEntryMax` (D13's Goal 4).
-/
import Rho5.Shared.TraceExistence.Existence

namespace Rho5.TraceExistence

open Rho5

/-- **Item 3.** A noncomputable choice of a complete legal trace for `A`.

This is `Classical.choose` applied to `exists_legalTrace`; it deliberately carries
no computation rule and must not be presented as an executable elimination
algorithm. -/
noncomputable def chosenTrace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : List ℝ :=
  Classical.choose (exists_legalTrace A)

/-- The chosen list is a legal trace. -/
theorem chosenTrace_spec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Rho5.CompletePivotPath.LegalTrace A (chosenTrace A) :=
  Classical.choose_spec (exists_legalTrace A)

/-- The chosen trace has at most `n` stages. -/
theorem chosenTrace_length_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (chosenTrace A).length ≤ n :=
  Rho5.CompletePivotPath.length_le (chosenTrace_spec A)

/-- At order `0` the chosen trace is the empty list: the terminal stage adds no
extra `0`. -/
theorem chosenTrace_eq_nil_of_order_zero (A : Matrix (Fin 0) (Fin 0) ℝ) :
    chosenTrace A = [] := by
  match h : chosenTrace A with
  | [] => rfl
  | v :: vs =>
      have hlen := chosenTrace_length_le A
      rw [h] at hlen
      exact absurd hlen (by simp)

/-- At a positive-order zero matrix the chosen trace is `[0]` (D13's `zero_iff`). -/
theorem chosenTrace_zero_eq_singleton {n : ℕ} :
    chosenTrace (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = [0] :=
  Rho5.CompletePivotPath.zero_iff.mp (chosenTrace_spec _)

/-- At positive order the chosen trace is nonempty. -/
theorem chosenTrace_ne_nil {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    chosenTrace A ≠ [] :=
  Rho5.CompletePivotPath.ne_nil_of_pos (chosenTrace_spec A)

/-- Every value recorded by the chosen trace is nonnegative. -/
theorem chosenTrace_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ v ∈ chosenTrace A, 0 ≤ v :=
  Rho5.CompletePivotPath.nonneg (chosenTrace_spec A)

/-- **Item 3/4 (`Matrix5`).** For a nonzero `5 × 5` matrix the chosen trace is
nonempty and its head is the frozen entry maximum. -/
theorem chosenTrace5_head (A : Matrix5) (hA : A ≠ 0) :
    ∃ vs, chosenTrace A = matrixEntryMax A :: vs := by
  cases h : chosenTrace A with
  | nil => exact absurd h (chosenTrace_ne_nil A)
  | cons v vs =>
      refine ⟨vs, ?_⟩
      have hspec : Rho5.CompletePivotPath.LegalTrace A (v :: vs) := by
        rw [← h]
        exact chosenTrace_spec A
      rw [Rho5.CompletePivotPath.head_eq_matrixEntryMax hA hspec]

end Rho5.TraceExistence
