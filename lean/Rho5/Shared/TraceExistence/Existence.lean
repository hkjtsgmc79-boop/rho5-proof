/-
D14 — every matrix admits a complete legal elimination trace
============================================================

D13 defined the actual relation `Rho5.CompletePivotPath.LegalTrace` (the list of
successive pivot absolute values of a legal complete-pivot elimination) but
deliberately did **not** prove that any trace exists.  This module closes exactly
that gap, using D12's stagewise legal-pivot existence and nothing else:

* `exists_legalTrace` — for every `n` and every `A : Matrix (Fin n) (Fin n) ℝ`
  there is a list `values` with `LegalTrace A values`;
* `exists_legalTrace_cons` — a *chosen* legal pivot `(p, q)` with `A p q ≠ 0` can be
  the first step of a complete trace;
* `exists_legalTrace_cons_of_isCompletePivot` — the same for **every** legal complete
  pivot of a nonzero matrix, so no tie-break rule is privileged;
* `exists_legalTrace_ne_nil` — at positive order the trace can be taken nonempty.

The induction is on the order.  The three cases are the three D13 constructors:
`n = 0` uses `empty` (a `0 × 0` matrix is the zero matrix), the positive-order zero
matrix uses `zeroStop`, and a nonzero positive-order matrix uses
`Rho5.MatrixStage.exists_nonzero_completePivot` to obtain an actual legal nonzero
pivot and then `step` with the frozen D10 update `Rho5.PivotReindex.pivotSchur`.
No existence hypothesis is added: the only external ingredient is D12's proved
finite pivot existence.
-/
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixStage
import Rho5.Shared.CompletePivotPath

namespace Rho5.TraceExistence

open Rho5

/-- **Item 1.** Every real `n × n` matrix admits a complete legal elimination trace.

Proof by induction on the order:
* `n = 0`: the `0 × 0` matrix is the zero matrix, so `LegalTrace.empty` applies and
  the trace is `[]` (no extra terminal `0`);
* `n + 1` with `A = 0`: `zeroStop`, trace `[0]`;
* `n + 1` with `A ≠ 0`: D12 gives an actual `(p, q)` with `IsCompletePivot A p q` and
  `A p q ≠ 0`; the induction hypothesis applied to the frozen D10 update
  `pivotSchur A p q` gives the tail, and `LegalTrace.step` prepends `|A p q|`. -/
theorem exists_legalTrace : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ),
    ∃ values, Rho5.CompletePivotPath.LegalTrace A values
  | 0, A => by
      refine ⟨[], ?_⟩
      rw [show A = 0 from funext fun i => Fin.elim0 i]
      exact Rho5.CompletePivotPath.LegalTrace.empty
  | n + 1, A => by
      by_cases hA : A = 0
      · exact ⟨[0], by rw [hA]; exact Rho5.CompletePivotPath.LegalTrace.zeroStop rfl⟩
      · obtain ⟨p, q, hmax, hne⟩ := Rho5.MatrixStage.exists_nonzero_completePivot A hA
        obtain ⟨tail, htail⟩ := exists_legalTrace (Rho5.PivotReindex.pivotSchur A p q)
        exact ⟨|A p q| :: tail,
          Rho5.CompletePivotPath.LegalTrace.step p q hmax hne htail⟩

/-- **Item 2 (arbitrary chosen first pivot).** If `(p, q)` is a legal complete pivot
with nonzero value, then some complete trace *starts* with it.  The witness `(p, q)`
is an input of the statement, so this is not a claim about one fixed tie-break
choice. -/
theorem exists_legalTrace_cons {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) (hmax : Rho5.Pivot.IsCompletePivot A p q) (hne : A p q ≠ 0) :
    ∃ values, Rho5.CompletePivotPath.LegalTrace A (|A p q| :: values) := by
  obtain ⟨tail, htail⟩ := exists_legalTrace (Rho5.PivotReindex.pivotSchur A p q)
  exact ⟨tail, Rho5.CompletePivotPath.LegalTrace.step p q hmax hne htail⟩

/-- **Item 2 (every legal pivot of a nonzero matrix).** For a nonzero matrix, *any*
legal complete pivot — in particular every tied maximizer — can be the first step of
a complete trace.  The nonzero-pivot qualification is derived from D12's
`completePivot_ne_zero`, not assumed. -/
theorem exists_legalTrace_cons_of_isCompletePivot {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A ≠ 0) (p q : Fin (n + 1))
    (hmax : Rho5.Pivot.IsCompletePivot A p q) :
    ∃ values, Rho5.CompletePivotPath.LegalTrace A (|A p q| :: values) :=
  exists_legalTrace_cons A p q hmax (Rho5.MatrixStage.completePivot_ne_zero A hA p q hmax)

/-- At positive order the trace given by `exists_legalTrace` can be taken nonempty
(the zero matrix stops at `[0]`, a nonzero matrix steps). -/
theorem exists_legalTrace_ne_nil {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ∃ values, values ≠ [] ∧ Rho5.CompletePivotPath.LegalTrace A values := by
  obtain ⟨values, htrace⟩ := exists_legalTrace A
  exact ⟨values, Rho5.CompletePivotPath.ne_nil_of_pos htrace, htrace⟩

/-- The head of an existing trace is the largest absolute entry (D13's Goal 2), in
the form later stages consume: for a positive-order matrix, the *existence* result
already determines the first recorded value up to the maximum. -/
theorem exists_legalTrace_head_isMax {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ∃ v vs, Rho5.CompletePivotPath.LegalTrace A (v :: vs) ∧
      (∀ i j, |A i j| ≤ v) ∧ ∃ p q, |A p q| = v := by
  obtain ⟨values, htrace⟩ := exists_legalTrace_ne_nil A
  cases hvalues : values with
  | nil => exact absurd hvalues (by simpa using htrace.1)
  | cons v vs =>
      refine ⟨v, vs, ?_, ?_⟩
      · rw [← hvalues]; exact htrace.2
      · exact Rho5.CompletePivotPath.head_isMax (by rw [← hvalues]; exact htrace.2)

end Rho5.TraceExistence
