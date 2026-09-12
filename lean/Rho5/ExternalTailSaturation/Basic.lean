import Rho5.Certificate.B24Extraction.Extract
import Rho5.Shared.CompletePivotPath
import Rho5.Shared.GrowthModel.Scalar
import Rho5.Shared.TraceSigns.Definitions
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

/-!
Actual-matrix input and the honest five-step leading trace.
`height` below is |w - t*s/r| for an arbitrary tail.  In particular it is NOT
B24Extraction.F, whose r+s*t/r convention belongs to the balanced negative-D chart.
No hypothesis on the sign of the fourth pivot is imposed.
-/
noncomputable section
namespace Rho5.ExternalTailSaturation

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.Pivot (IsCompletePivot)
open Rho5.CompletePivotPath (LegalTrace)

/-- Actual bottom-right entry of the third Schur complement. -/
def w (M : Matrix5) : ℝ := T2 M 1 1
/-- Actual signed fifth pivot, using total real division only as a definition. -/
def delta (M : Matrix5) : ℝ := w M - t M * s M / r M
/-- Magnitude of the actual fifth pivot. -/
def height (M : Matrix5) : ℝ := |delta M|

/-- Exactly the requested leading-path input; no transformed feasibility field. -/
structure LeadingInput (M : Matrix5) : Prop where
  head : M 0 0 = 1
  cp0 : IsCompletePivot M 0 0
  cp1 : IsCompletePivot (S4 M) 0 0
  cp2 : IsCompletePivot (S3 M) 0 0
  cp3 : IsCompletePivot (T2 M) 0 0
  p_pos : 0 < p M
  k_pos : 0 < k M
  delta_ne : delta M ≠ 0

theorem r_ne_zero {M : Matrix5} (h : LeadingInput M) : r M ≠ 0 := by
  intro hr
  have hz : ∀ i j, T2 M i j = 0 :=
    Rho5.Pivot.zero_complete_pivot (T2 M) 0 0 h.cp3 hr
  apply h.delta_ne
  simp [delta, w, r, s, t, hz]

theorem height_pos {M : Matrix5} (h : LeadingInput M) : 0 < height M :=
  abs_pos.mpr h.delta_ne

theorem tail_bounds {M : Matrix5} (h : LeadingInput M) :
    |s M| ≤ |r M| ∧ |t M| ≤ |r M| ∧ |w M| ≤ |r M| :=
  ⟨h.cp3 0 1, h.cp3 1 0, h.cp3 1 1⟩

/-- Unit entry maximum follows from the actual complete pivot, not from a chart. -/
theorem entryMax_eq_one (M : Matrix5) (h00 : M 0 0 = 1)
    (hcp : IsCompletePivot M 0 0) : matrixEntryMax M = 1 := by
  apply le_antisymm
  · unfold matrixEntryMax
    refine Finset.sup'_le Finset.univ_nonempty _ (fun ij _ => ?_)
    simpa [h00] using hcp ij.1 ij.2
  · have h := Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax M 0 0
    simpa [h00] using h

/-- The actual 1-by-1 last Schur block. -/
def U1 (M : Matrix5) : Matrix (Fin 1) (Fin 1) ℝ :=
  Rho5.PivotReindex.pivotSchur (T2 M) 0 0

theorem U1_zero_zero (M : Matrix5) : U1 M 0 0 = delta M := by
  exact (Rho5.PivotReindex.pivotSchur_fin_two (T2 M)).1

theorem U1_cp (M : Matrix5) : IsCompletePivot (U1 M) 0 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  exact le_rfl

/-- Empty terminal matrix; no artificial extra zero in the value list. -/
theorem U1_schur_zero (M : Matrix5) :
    Rho5.PivotReindex.pivotSchur (U1 M) 0 0 =
      (0 : Matrix (Fin 0) (Fin 0) ℝ) := by
  funext i j
  exact Fin.elim0 i

/-- Five genuine nonzero LegalTrace.step constructors followed by LegalTrace.empty. -/
theorem leading_legalTrace {M : Matrix5} (h : LeadingInput M) :
    LegalTrace M [1, p M, k M, |r M|, height M] := by
  have hU : U1 M 0 0 ≠ 0 := by rw [U1_zero_zero]; exact h.delta_ne
  have hlast : LegalTrace (U1 M) [|U1 M 0 0|] := by
    refine LegalTrace.step (0 : Fin 1) 0 (U1_cp M) hU ?_
    rw [U1_schur_zero]
    exact LegalTrace.empty
  have htail : LegalTrace (T2 M) [|T2 M 0 0|, |U1 M 0 0|] :=
    LegalTrace.step (0 : Fin 2) 0 h.cp3 (r_ne_zero h) hlast
  have hthird : LegalTrace (S3 M) [|S3 M 0 0|, |T2 M 0 0|, |U1 M 0 0|] :=
    LegalTrace.step (0 : Fin 3) 0 h.cp2 (ne_of_gt h.k_pos) htail
  have hsecond : LegalTrace (S4 M)
      [|S4 M 0 0|, |S3 M 0 0|, |T2 M 0 0|, |U1 M 0 0|] :=
    LegalTrace.step (0 : Fin 4) 0 h.cp1 (ne_of_gt h.p_pos) hthird
  have hfirst : LegalTrace M
      [|M 0 0|, |S4 M 0 0|, |S3 M 0 0|, |T2 M 0 0|, |U1 M 0 0|] :=
    LegalTrace.step (0 : Fin 5) 0 h.cp0 (by rw [h.head]; norm_num) hsecond
  have hpabs : |S4 M 0 0| = p M := abs_of_pos h.p_pos
  have hkabs : |S3 M 0 0| = k M := abs_of_pos h.k_pos
  simpa only [h.head, abs_one, hpabs, hkabs, U1_zero_zero] using hfirst

/-- Convenience entry point with all eight original hypotheses visible. -/
theorem leading_legalTrace_explicit (M : Matrix5) (h00 : M 0 0 = 1)
    (h0 : IsCompletePivot M 0 0) (h1 : IsCompletePivot (S4 M) 0 0)
    (h2 : IsCompletePivot (S3 M) 0 0) (h3 : IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hd : delta M ≠ 0) :
    LegalTrace M [1, p M, k M, |r M|, height M] :=
  leading_legalTrace ⟨h00, h0, h1, h2, h3, hp, hk, hd⟩

end Rho5.ExternalTailSaturation
