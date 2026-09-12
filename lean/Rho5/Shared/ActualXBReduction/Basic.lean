/-
D126 — the X-branch payload: a `SatFrame` matrix realizes an honest `V43.Physical` X22 point
===========================================================================================

This module is the part of the card that is payable **now**, without the D123/D125 gates: the whole
X-side content of the final assembly, stated over D119's `SatFrame` class instead of over the frozen
TS structures.

For a `SatFrame` matrix `N` (normalization + four leading complete pivots + `p, k, r > 0` + the
saturated tail `s = t = r`, general `w`) D119 produces the reverse point `x = extractX N` with
`V43.Physical x`, `reconstruct x = N` and `height x = |CanonicalTail.delta N|`.  Here that witness is
assembled **together with every reading the card demands**, so that the final `X` branch is a
concrete matrix-level statement rather than an abstract coordinate existence:

* the witness is the actual matrix `reconstruct x = N`, not a formal placeholder;
* the pivots are preserved: `p (reconstruct x) = p N`, `k (reconstruct x) = k N`,
  `r (reconstruct x) = r N`, with `0 < r (reconstruct x)` and `r (reconstruct x) ≤ |r N|`;
* the reconstruction is normalized (`matrixEntryMax (reconstruct x) = 1`) and carries a **real**
  `LegalTrace` with value list `[1, p N, k N, r N, |delta N|]`;
* its growth ratio is at least `|CanonicalTail.delta N|`.

The last two items are the honest replacement for a vague "peak equality": they are D103's actual
`legalTrace_M`/`growthRatio_ge_height` instantiated at the extracted point, with the coordinate
readings rewritten into the given matrix's own pivot readings.

Scope: `SatFrame` carries no cube membership and no claim that global maximizers lie in it; the
general `w` is kept throughout.
-/
import Rho5.Shared.V43MatrixRoundTrip

namespace Rho5.Shared.ActualXBReduction

noncomputable section
set_option maxHeartbeats 800000

open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- The reverse point of a saturated frame, in the fixed X22 order. -/
abbrev xPoint (N : Rho5.Matrix5) : Rho5.LocalAnalysis.X :=
  Rho5.Shared.V43MatrixRoundTrip.extractX N

/-- The accepted D103 reconstruction, re-exported under a distinct name. -/
abbrev reconstruct (x : Rho5.LocalAnalysis.X) : Rho5.Matrix5 :=
  Rho5.Shared.V43MatrixRoundTrip.reconstruct x

/-! ## 1. The witness and its coordinate-level readings -/

/-- **The X witness.**  A saturated frame is realized by its own reverse point: the point is
`V43.Physical`, it reconstructs back to the *same* matrix `N`, and its height is exactly
`|CanonicalTail.delta N|`. -/
theorem exists_physical_of_satFrame (N : Rho5.Matrix5)
    (h : Rho5.Shared.V43MatrixRoundTrip.SatFrame N) :
    ∃ x : Rho5.LocalAnalysis.X, Rho5.LocalAnalysis.V43.Physical x ∧
      reconstruct x = N ∧ Rho5.LocalAnalysis.height x = |Rho5.CanonicalTail.delta N| :=
  ⟨xPoint N, Rho5.Shared.V43MatrixRoundTrip.physical_extractX N h,
    Rho5.Shared.V43MatrixRoundTrip.reconstruct_extractX N h,
    Rho5.Shared.V43MatrixRoundTrip.height_extractX N h⟩

/-- The witness is physical. -/
theorem physical_xPoint (N : Rho5.Matrix5) (h : Rho5.Shared.V43MatrixRoundTrip.SatFrame N) :
    Rho5.LocalAnalysis.V43.Physical (xPoint N) :=
  Rho5.Shared.V43MatrixRoundTrip.physical_extractX N h

/-- The witness reconstructs to the given matrix. -/
theorem reconstruct_xPoint (N : Rho5.Matrix5) (h : Rho5.Shared.V43MatrixRoundTrip.SatFrame N) :
    reconstruct (xPoint N) = N :=
  Rho5.Shared.V43MatrixRoundTrip.reconstruct_extractX N h

/-- The witness's height is the frozen δ of the given matrix. -/
theorem height_xPoint (N : Rho5.Matrix5) (h : Rho5.Shared.V43MatrixRoundTrip.SatFrame N) :
    Rho5.LocalAnalysis.height (xPoint N) = |Rho5.CanonicalTail.delta N| :=
  Rho5.Shared.V43MatrixRoundTrip.height_extractX N h

/-- **Pivot preservation, `p`.**  The reconstruction's first pivot is the given matrix's. -/
theorem p_xPoint (N : Rho5.Matrix5) (h : Rho5.Shared.V43MatrixRoundTrip.SatFrame N) :
    p (reconstruct (xPoint N)) = p N := by
  rw [reconstruct_xPoint N h]

/-- **Pivot preservation, `k`.** -/
theorem k_xPoint (N : Rho5.Matrix5) (h : Rho5.Shared.V43MatrixRoundTrip.SatFrame N) :
    k (reconstruct (xPoint N)) = k N := by
  rw [reconstruct_xPoint N h]

/-- **Pivot preservation, `r`.** -/
theorem r_xPoint (N : Rho5.Matrix5) (h : Rho5.Shared.V43MatrixRoundTrip.SatFrame N) :
    r (reconstruct (xPoint N)) = r N := by
  rw [reconstruct_xPoint N h]

/-- The fourth pivot of the witness is positive. -/
theorem r_xPoint_pos (N : Rho5.Matrix5) (h : Rho5.Shared.V43MatrixRoundTrip.SatFrame N) :
    0 < r (reconstruct (xPoint N)) := by
  rw [r_xPoint N h]
  exact h.hr

/-- The fourth pivot of the witness does not exceed the given `|r N|`. -/
theorem r_xPoint_le_abs (N : Rho5.Matrix5) (h : Rho5.Shared.V43MatrixRoundTrip.SatFrame N) :
    r (reconstruct (xPoint N)) ≤ |r N| := by
  rw [r_xPoint N h]
  exact le_abs_self _

/-- **Normalization of the witness.**  The reconstruction has unit entry maximum. -/
theorem entryMax_xPoint (N : Rho5.Matrix5) (h : Rho5.Shared.V43MatrixRoundTrip.SatFrame N) :
    Rho5.matrixEntryMax (reconstruct (xPoint N)) = 1 := by
  rw [reconstruct_xPoint N h]
  exact h.hmax

/-! ## 2. The real legal trace and growth of the witness -/

/-- The witness's own value list, in the given matrix's pivot readings. -/
theorem traceValues_xPoint (N : Rho5.Matrix5)
    (h : Rho5.Shared.V43MatrixRoundTrip.SatFrame N) :
    Rho5.Shared.V43ActualMatrix.traceValues (xPoint N)
      = [1, p N, k N, r N, |Rho5.CanonicalTail.delta N|] := by
  simp only [Rho5.Shared.V43ActualMatrix.traceValues, Rho5.Shared.V43ActualMatrix.pOf,
    Rho5.Shared.V43ActualMatrix.kOf, Rho5.Shared.V43ActualMatrix.rOf,
    Rho5.Shared.V43ActualMatrix.wOf, Rho5.Shared.V43MatrixRoundTrip.extractX_7,
    Rho5.Shared.V43MatrixRoundTrip.extractX_0, Rho5.Shared.V43MatrixRoundTrip.extractX_1,
    Rho5.Shared.V43MatrixRoundTrip.extractX_2, Rho5.Shared.V43MatrixRoundTrip.pX_eq_p,
    Rho5.Shared.V43MatrixRoundTrip.kX_eq_k, Rho5.Shared.V43MatrixRoundTrip.rX_eq_r]
  have hd : Rho5.Shared.V43MatrixRoundTrip.wX N - r N = Rho5.CanonicalTail.delta N := by
    rw [← Rho5.Shared.V43MatrixRoundTrip.rX_eq_r,
      ← Rho5.Shared.V43MatrixRoundTrip.delta_eq_wX_sub_rX N h]
  rw [hd]

/-- **A real `LegalTrace` of the given matrix itself.**  The saturated frame `N` carries the actual
frozen-D13 elimination trace `[1, p N, k N, r N, |delta N|]` — every entry a real pivot value of
`N`, obtained from D103's `legalTrace_M` at the extracted point and rewritten through D119's
round trip. -/
theorem legalTrace_N (N : Rho5.Matrix5) (h : Rho5.Shared.V43MatrixRoundTrip.SatFrame N) :
    Rho5.CompletePivotPath.LegalTrace N [1, p N, k N, r N, |Rho5.CanonicalTail.delta N|] := by
  have hm : Rho5.Shared.V43ActualMatrix.M (xPoint N) = N :=
    Rho5.Shared.V43MatrixRoundTrip.reconstruct_extractX N h
  have htr := Rho5.Shared.V43ActualMatrix.legalTrace_M (xPoint N) (physical_xPoint N h)
  rwa [hm, traceValues_xPoint N h] at htr

/-- **Growth of the given matrix.**  Its growth ratio is at least `|delta N|` — D103's
`growthRatio_ge_height` at the extracted point, with the height rewritten through D119's reading.
This is the honest replacement for a vague peak equality: it names the actual trace and the actual
growth ratio of `N`. -/
theorem growth_ge_delta_N (N : Rho5.Matrix5) (h : Rho5.Shared.V43MatrixRoundTrip.SatFrame N) :
    |Rho5.CanonicalTail.delta N| ≤ Rho5.GrowthModel.growthRatio N
      [1, p N, k N, r N, |Rho5.CanonicalTail.delta N|] := by
  have hm : Rho5.Shared.V43ActualMatrix.M (xPoint N) = N :=
    Rho5.Shared.V43MatrixRoundTrip.reconstruct_extractX N h
  have hg := Rho5.Shared.V43ActualMatrix.growthRatio_ge_height (xPoint N) (physical_xPoint N h)
  rwa [hm, traceValues_xPoint N h, height_xPoint N h] at hg

end

end Rho5.Shared.ActualXBReduction
