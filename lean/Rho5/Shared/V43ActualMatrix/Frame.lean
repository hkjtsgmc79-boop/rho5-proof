/-
D103 — stage B (3/3): the reconstruction `M x` lies in the division-free polynomial domain `PolyCP`
===================================================================================================

The frozen D62 interface `Rho5.MinorCPDomain.polyCP_iff_frame` states that, under `M 0 0 = 1`, the
division-free polynomial system `PolyCP M` (positivity of the three bordered-minor pivots
`A = m2 0 0`, `B = m3 0 0`, `C = m4 0 0`, the 25 entry bounds, and the 16/9/4 bordered-minor bounds)
is **equivalent** to the actual frame: `matrixEntryMax M = 1`, the four leading complete pivots on
`M`, `S4 M`, `S3 M`, `T2 M`, and `p M, k M, r M > 0`.

This file feeds the frame proved in `Pivot.lean` into that equivalence, so `PolyCP (M x)` is paid
as a *compatible interface*, not asserted: `matrixEntryMax (M x) = 1` (stage A), the four complete
pivots (`isCompletePivot_M/S4/S3/T2`), and the three positivity readings (`p_M_pos`, `k_M_pos`,
`r_M_pos`, i.e. `p (M x) = x 7`, `k (M x) = x 0`, `r (M x) = x 1` from `V43.Physical`).

No new inequality system is introduced here, no Schur update is re-expanded, and the general `w`
is untouched.
-/
import Rho5.Shared.V43ActualMatrix.Pivot
import Rho5.Shared.MinorCPDomain.Poly

namespace Rho5.Shared.V43ActualMatrix

noncomputable section
set_option maxHeartbeats 800000

open Rho5.Certificate.B24Extraction (S4 S3 T2)

/-- **The actual frame of the reconstruction**, as the tuple the frozen D62 equivalence consumes. -/
theorem frame_M (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.matrixEntryMax (M x) = 1 ∧ Rho5.Pivot.IsCompletePivot (M x) 0 0 ∧
      Rho5.Pivot.IsCompletePivot (S4 (M x)) 0 0 ∧
      Rho5.Pivot.IsCompletePivot (S3 (M x)) 0 0 ∧
      Rho5.Pivot.IsCompletePivot (T2 (M x)) 0 0 ∧
      0 < Rho5.Certificate.B24Extraction.p (M x) ∧
      0 < Rho5.Certificate.B24Extraction.k (M x) ∧
      0 < Rho5.Certificate.B24Extraction.r (M x) :=
  ⟨matrixEntryMax_eq_one x hx, isCompletePivot_M x hx, isCompletePivot_S4 x hx,
    isCompletePivot_S3 x hx, isCompletePivot_T2 x hx,
    p_M_pos x hx, k_M_pos x hx, r_M_pos x hx⟩

/-- **`PolyCP` compatibility interface.**  The actual reconstruction of a `V43.Physical` point lies
in the frozen D62 division-free polynomial domain, through the paid equivalence
`polyCP_iff_frame` and the actual frame `frame_M`. -/
theorem polyCP_M (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.MinorCPDomain.PolyCP (M x) :=
  (Rho5.MinorCPDomain.polyCP_iff_frame (M x) (M_zero_zero x)).mpr (frame_M x hx)

end

end Rho5.Shared.V43ActualMatrix
