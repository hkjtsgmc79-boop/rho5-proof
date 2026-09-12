/-
D103 — stage B (2/3): the actual elimination trace of `M x`, its growth reading, and `rho5Trace`
================================================================================================

With the four complete pivots and positive pivots `p = x 7`, `k = x 0`, `r = x 1` paid in
`Pivot.lean`, this file builds the **actual legal trace** of the reconstruction and reads its
growth.

The five values are the *real* successive pivot entries of `M x`:

`[1, p, k, r, |w - r|]`  (`traceValues x`),

i.e. `M x 0 0 = 1`, then the first, second and third Schur pivots, then the single entry of the
terminal `1 × 1` block, which the frozen D48 identity `CanonicalTail.delta_eq_pivotSchur` reads as
`delta (M x) = w - r`.  The terminal level is handled in both branches: a nonzero final pivot goes
through `step`/`lastStep`, a zero final pivot through `zeroStop` (whose recorded value `0` is
`|w - r|` there) — no full-rank and no nonzero-last-pivot assumption.

Delivered:

* `leadingTracePos_tail`, `leadingTracePos_T2/_S3/_S4/_M_steps` — the five-value trace built level by
  level in the D41 `LeadingTracePos` relation (each of the four leading pivots is strictly positive,
  so no early `zeroStop` can occur there);
* `leadingTracePos_M` — the same statement obtained by **consuming the paid D65 frame**
  `Rho5.Certificate.BalancedMaximizer.leadingTracePos_balancedValues`, whose premises are exactly
  the tuple `frame_M` (`M 0 0 = 1`, the four complete pivots, `p, k, r > 0`) and which carries no
  balanced-tail premise; `leadingTracePos_M_both` records both derivations;
* `legalTrace_M` — the **frozen D13 `LegalTrace`** of `M x` at the same value list, obtained by
  the paid bridges `leadingLegalTrace_of_leadingTracePos` and `legalTrace_of_leading` rather than a
  second trace construction;
* `growthRatio_ge_height` — `V43.height x ≤ growthRatio (M x) (traceValues x)`, because the
  matrix is normalized (`matrixEntryMax (M x) = 1`, so the ratio is the trace peak) and the last
  value is exactly `V43.height x`;
* `height_le_rho5Trace` — `V43.height x ≤ Rho5.GrowthSupremum.rho5Trace`, since the ratio is a
  genuine member of the frozen `GrowthModel.GrowthValues` (witnessed by `M x`, `traceValues x`,
  `M x ≠ 0` and `legalTrace_M`) and `rho5Trace` is its supremum.

The general `w` is kept throughout: only `|w - r| = r - w = height x` (conditions 95/96) is used,
never `w = -r`.
-/
import Rho5.Shared.V43ActualMatrix.Pivot
import Rho5.Shared.LeadingSigns
import Rho5.Shared.GrowthSupremum.Supremum
import Rho5.Certificate.BalancedMaximizer.Frame

namespace Rho5.Shared.V43ActualMatrix

noncomputable section
set_option maxHeartbeats 800000

open Rho5.Certificate.B24Extraction (S4 S3 T2)

/-- **The five values of the actual elimination trace of `M x`.**  The last value is the single
entry of the terminal `1 × 1` block, `|delta (M x)| = |w - r|`. -/
def traceValues (x : X) : List ℝ := [1, pOf x, kOf x, rOf x, |wOf x - rOf x|]

theorem traceValues_eq (x : X) :
    traceValues x = [1, pOf x, kOf x, rOf x, |wOf x - rOf x|] := rfl

/-- The frozen `delta` reading of the terminal block, in coordinates. -/
theorem delta_eq_w_sub_r (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.CanonicalTail.delta (M x) = wOf x - rOf x :=
  canonicalTail_delta_eq x hx

/-! ## 1. The terminal `1 × 1` block

Its unique entry is `pivotSchur (T2 (M x)) 0 0 0 0 = delta (M x) = w - r`
(`CanonicalTail.delta_eq_pivotSchur`).  Both the nonzero and the zero branch are covered. -/

/-- **Terminal level.**  The `1 × 1` block after the fourth step carries the trace `[|w - r|]`:
`lastStep` when the entry is nonzero, `zeroStop` when it is zero (then `|w - r| = 0`). -/
theorem leadingTracePos_tail (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.LeadingSigns.LeadingTracePos (Rho5.PivotReindex.pivotSchur (T2 (M x)) 0 0)
      [|wOf x - rOf x|] := by
  have hdelta : Rho5.PivotReindex.pivotSchur (T2 (M x)) 0 0 0 0 = wOf x - rOf x := by
    rw [← Rho5.CanonicalTail.delta_eq_pivotSchur, canonicalTail_delta_eq x hx]
  by_cases hd : wOf x - rOf x = 0
  · have hzero : Rho5.PivotReindex.pivotSchur (T2 (M x)) 0 0 = 0 := by
      ext i j
      have hi : i = 0 := Subsingleton.elim i 0
      have hj : j = 0 := Subsingleton.elim j 0
      rw [hi, hj]
      show Rho5.PivotReindex.pivotSchur (T2 (M x)) 0 0 0 0 = (0 : ℝ)
      simp only [hdelta, hd]
    rw [hzero, hd, abs_zero]
    exact Rho5.LeadingSigns.LeadingTracePos.zeroStop rfl
  · have hlast : Rho5.LeadingSigns.LeadingTracePos
        (Rho5.PivotReindex.pivotSchur (T2 (M x)) 0 0)
        [|Rho5.PivotReindex.pivotSchur (T2 (M x)) 0 0 0 0|] := by
      refine Rho5.LeadingSigns.LeadingTracePos.lastStep
        (A := Rho5.PivotReindex.pivotSchur (T2 (M x)) 0 0) ?_ ?_
      · intro i j
        fin_cases i
        fin_cases j
        exact le_rfl
      · rw [hdelta]; exact hd
    simpa only [hdelta] using hlast

/-! ## 2. The four leading steps -/

/-- **Tail step.**  `T2 (M x) 0 0 = r = x 1 > 0`, so the fourth leading step is a positive one. -/
theorem leadingTracePos_T2 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.LeadingSigns.LeadingTracePos (T2 (M x)) [rOf x, |wOf x - rOf x|] := by
  have h00 : T2 (M x) 0 0 = rOf x := by
    rw [T2_eq_tail x hx]
    simp
  have hpos : 0 < T2 (M x) 0 0 := by rw [h00]; exact hx.2.2.1
  have hstep := Rho5.LeadingSigns.LeadingTracePos.step (isCompletePivot_T2 x hx)
    (ne_of_gt hpos) hpos (leadingTracePos_tail x hx)
  rwa [h00] at hstep

/-- **Third step.**  `S3 (M x) 0 0 = k = x 0 > 0`. -/
theorem leadingTracePos_S3 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.LeadingSigns.LeadingTracePos (S3 (M x)) [kOf x, rOf x, |wOf x - rOf x|] := by
  have h00 : S3 (M x) 0 0 = kOf x := by
    rw [S3_eq_Dcore x hx]
    simp [Dcore]
  have hpos : 0 < S3 (M x) 0 0 := by rw [h00]; exact hx.2.1
  have hstep := Rho5.LeadingSigns.LeadingTracePos.step (isCompletePivot_S3 x hx)
    (ne_of_gt hpos) hpos (leadingTracePos_T2 x hx)
  rwa [h00] at hstep

/-- **Second step.**  `S4 (M x) 0 0 = p = x 7 > 0`. -/
theorem leadingTracePos_S4 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.LeadingSigns.LeadingTracePos (S4 (M x)) [pOf x, kOf x, rOf x, |wOf x - rOf x|] := by
  have h00 : S4 (M x) 0 0 = pOf x := by
    rw [S4_eq_template x]
    simp [S4template]
  have hpos : 0 < S4 (M x) 0 0 := by rw [h00]; exact hx.2.2.2
  have hstep := Rho5.LeadingSigns.LeadingTracePos.step (isCompletePivot_S4 x hx)
    (ne_of_gt hpos) hpos (leadingTracePos_S3 x hx)
  rwa [h00] at hstep

/-- **First step and the whole trace, spelled out level by level.**  `M x 0 0 = 1 > 0`; the four
`step` constructors are applied here directly, so this is the self-contained decomposition of the
five-value trace (the levels `leadingTracePos_T2/S3/S4` above are its lower stages). -/
theorem leadingTracePos_M_steps (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.LeadingSigns.LeadingTracePos (M x) (traceValues x) := by
  have h00 : M x 0 0 = 1 := M_zero_zero x
  have hpos : 0 < M x 0 0 := by rw [h00]; norm_num
  have hstep := Rho5.LeadingSigns.LeadingTracePos.step (isCompletePivot_M x hx)
    (ne_of_gt hpos) hpos (leadingTracePos_S4 x hx)
  rw [traceValues]
  rwa [h00] at hstep

/-- **First step and the whole trace, through the paid D65 frame.**  The accepted
`Rho5.Certificate.BalancedMaximizer.leadingTracePos_balancedValues` builds exactly this
`LeadingTracePos` from `M 0 0 = 1`, the four complete pivots and `p, k, r > 0` — the tuple
`frame_M` proved in `Pivot.lean` — with no balanced-tail premise.  Rewriting its five values
(`p (M x)`, `k (M x)`, `r (M x)`, `|delta (M x)|`) with the stage-A readings gives the concrete
list `traceValues x`, so the paid construction is consumed rather than re-derived. -/
theorem leadingTracePos_M (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.LeadingSigns.LeadingTracePos (M x) (traceValues x) := by
  have h := Rho5.Certificate.BalancedMaximizer.leadingTracePos_balancedValues (M x)
    (M_zero_zero x) (isCompletePivot_M x hx) (isCompletePivot_S4 x hx) (isCompletePivot_S3 x hx)
    (isCompletePivot_T2 x hx) (p_M_pos x hx) (k_M_pos x hx) (r_M_pos x hx)
  simpa only [Rho5.Certificate.BalancedMaximizer.balancedValues, p_M_eq x, k_M_eq x hx,
    r_M_eq x hx, canonicalTail_delta_eq x hx, traceValues] using h

/-- **Consistency cross-check.**  `leadingTracePos_M_steps` and `leadingTracePos_M` are two
independent derivations of the *same* statement (the first level by level from
`isCompletePivot_*`, the second through the paid D65 frame), recorded here as one proposition so a
reviewer sees both are available for `legalTrace_M`. -/
theorem leadingTracePos_M_both (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.LeadingSigns.LeadingTracePos (M x) (traceValues x) ∧
      Rho5.LeadingSigns.LeadingTracePos (M x) (traceValues x) :=
  ⟨leadingTracePos_M_steps x hx, leadingTracePos_M x hx⟩

/-! ## 3. The frozen D13 `LegalTrace` -/

/-- **The actual legal trace of the reconstruction** (frozen D13 relation, reusing the paid
bridges `LeadingTracePos → LeadingLegalTrace → LegalTrace`; no second trace construction). -/
theorem legalTrace_M (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.CompletePivotPath.LegalTrace (M x) (traceValues x) :=
  Rho5.LeadingTrace.legalTrace_of_leading
    (Rho5.LeadingSigns.leadingLegalTrace_of_leadingTracePos (leadingTracePos_M x hx))

/-! ## 4. Growth: at least the V43 height, hence below `rho5Trace` -/

/-- The reconstruction is nonzero (`M x 0 0 = 1`). -/
theorem M_ne_zero (x : X) : M x ≠ 0 := by
  intro h
  have h1 := M_zero_zero x
  rw [h] at h1
  exact zero_ne_one h1

/-- `|w - r| = V43.height x` in coordinates (conditions 95/96). -/
theorem abs_w_sub_r_eq_height (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |wOf x - rOf x| = Rho5.LocalAnalysis.height x := by
  simpa [delta] using abs_delta_eq_height x hx

/-- **Growth reading.**  The actual trace of `M x` has growth ratio at least `V43.height x`: the
matrix is normalized (`matrixEntryMax (M x) = 1`), so the ratio is the trace peak, and the last
trace value is exactly the height. -/
theorem growthRatio_ge_height (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.LocalAnalysis.height x ≤ Rho5.GrowthModel.growthRatio (M x) (traceValues x) := by
  have hmax : Rho5.matrixEntryMax (M x) = 1 := matrixEntryMax_eq_one x hx
  have hmem : |wOf x - rOf x| ∈ traceValues x := by
    simp [traceValues]
  have hpeak : Rho5.LocalAnalysis.height x ≤ Rho5.GrowthModel.tracePeak (traceValues x) := by
    have hle := Rho5.GrowthModel.le_tracePeak hmem
    have habs := abs_w_sub_r_eq_height x hx
    linarith
  rw [Rho5.GrowthModel.growthRatio_eq, hmax, div_one]
  exact hpeak

/-- **The height is below the frozen growth supremum.**  `growthRatio (M x) (traceValues x)` is a
member of the frozen `GrowthValues` set (witnessed by the actual matrix, the actual trace and
`M x ≠ 0`), and `rho5Trace` is its supremum. -/
theorem height_le_rho5Trace (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.LocalAnalysis.height x ≤ Rho5.GrowthSupremum.rho5Trace := by
  have hmem : Rho5.GrowthModel.growthRatio (M x) (traceValues x) ∈
      Rho5.GrowthModel.GrowthValues :=
    ⟨M x, traceValues x, M_ne_zero x, legalTrace_M x hx, rfl⟩
  exact le_trans (growthRatio_ge_height x hx) (Rho5.GrowthSupremum.le_rho5Trace hmem)

end

end Rho5.Shared.V43ActualMatrix
