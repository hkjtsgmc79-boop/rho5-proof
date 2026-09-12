/-
D14 — the `Matrix5` instance
============================

**Item 4.** The existence statement instantiated at the pilot's `5 × 5` matrix, with
the two head descriptions the later cards consume.  Everything is cited from D13 and
D08; no scaling proof is rewritten here.

* `exists_legalTrace5` — every `Matrix5` has a legal trace;
* `exists_legalTrace5_head` — for `A ≠ 0` the trace is nonempty with head
  `Rho5.matrixEntryMax A`;
* `exists_legalTrace5_normalize_head` — the normalized matrix also has a trace whose
  head is `1` (D13's `head_eq_one_of_normalize`);
* `exists_legalTrace5_normalize_map` — the normalized trace displayed as the scaled
  chosen trace through D13's whole-trace scaling equivalence
  `legalTrace_normalize_iff`.
-/
import Rho5.Shared.TraceExistence.Chosen
import Rho5.Shared.MatrixNormalization

namespace Rho5.TraceExistence

open Rho5

/-- **Item 4.** Every `5 × 5` real matrix admits a complete legal trace. -/
theorem exists_legalTrace5 (A : Matrix5) :
    ∃ values, Rho5.CompletePivotPath.LegalTrace A values :=
  exists_legalTrace A

/-- **Item 4 (nonzero case).** For a nonzero `5 × 5` matrix there is a legal trace
that is nonempty and whose head is the frozen entry maximum. -/
theorem exists_legalTrace5_head (A : Matrix5) (hA : A ≠ 0) :
    ∃ v vs, Rho5.CompletePivotPath.LegalTrace A (v :: vs) ∧ v = matrixEntryMax A := by
  obtain ⟨values, htrace⟩ := exists_legalTrace5 A
  cases hvalues : values with
  | nil => exact absurd hvalues (Rho5.CompletePivotPath.ne_nil_of_pos htrace)
  | cons v vs =>
      refine ⟨v, vs, ?_, ?_⟩
      · rw [← hvalues]; exact htrace
      · exact Rho5.CompletePivotPath.head_eq_matrixEntryMax hA (by rw [← hvalues]; exact htrace)

/-- **Item 4 (normalized head is `1`).** The unit-normalized `5 × 5` matrix has a
legal trace that is nonempty with head `1`. -/
theorem exists_legalTrace5_normalize_head (A : Matrix5) (hA : A ≠ 0) :
    ∃ v vs, Rho5.CompletePivotPath.LegalTrace (Rho5.MatrixNormalization.normalize A) (v :: vs) ∧
      v = 1 := by
  have hnorm : Rho5.MatrixNormalization.normalize A ≠ 0 :=
    Rho5.CompletePivotPath.normalize_ne_zero hA
  obtain ⟨v, vs, htrace, _⟩ := exists_legalTrace5_head _ hnorm
  exact ⟨v, vs, htrace, Rho5.CompletePivotPath.head_eq_one_of_normalize hA htrace⟩

/-- **Item 4 (normalized trace = scaled chosen trace).** The normalized matrix's
trace can be displayed through D13's scaling equivalence: the chosen trace of `A`
maps to a legal trace of `normalize A` by the factor `(matrixEntryMax A)⁻¹`. -/
theorem exists_legalTrace5_normalize_map (A : Matrix5) (hA : A ≠ 0) :
    ∃ values, Rho5.CompletePivotPath.LegalTrace (Rho5.MatrixNormalization.normalize A)
        (values.map (fun v => (matrixEntryMax A)⁻¹ * v)) ∧
      Rho5.CompletePivotPath.LegalTrace A values :=
  ⟨chosenTrace A,
   (Rho5.CompletePivotPath.legalTrace_normalize_iff A hA (chosenTrace A)).mpr
     (chosenTrace_spec A),
   chosenTrace_spec A⟩

/-- The `Matrix5` trace existence read through the chosen trace, for callers that
prefer a single canonical witness. -/
theorem exists_legalTrace5_chosen (A : Matrix5) :
    Rho5.CompletePivotPath.LegalTrace A (chosenTrace A) :=
  chosenTrace_spec A

end Rho5.TraceExistence
