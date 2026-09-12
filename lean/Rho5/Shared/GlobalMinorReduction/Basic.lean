/-
D69 — the forward direction of the global minor reduction.

**Statement.**  If `rho5Trace ≤ T`, then every actual matrix in the finite `PolyCP`
domain satisfies the two polynomial minor inequalities of D67.

**Proof.**  `PolyCP M` together with `M 0 0 = 1` is *equivalent* to the frame
`matrixEntryMax M = 1 ∧ four leading complete pivots ∧ 0 < p M, k M, r M` (D62's paid
`polyCP_iff_frame`) — this is the only place the finite domain is opened, and no second
domain is introduced.  That frame is exactly D55's nine qualifications, so D55's
`legalTrace_shift` at shift `0` yields an **actual** legal trace of `M` itself; its value
list is `traceValues M 0 = [1, p M, k M, r M, |delta M|]`, with the zero-final case
preserved (the tail trace is D46's arbitrary-tail one, which already covers a vanishing
last `1 × 1` pivot).

Hence `growthRatio M [1, p M, k M, r M, |delta M|]` is an actual member of D17's
`GrowthValues`, so it is at most `rho5Trace ≤ T`.  D67's `threshold_iff` turns that into
the two inequalities.

Nothing here assumes that an arbitrary low-growth matrix has a positive prefix, and no
existence, attainment, full-rank or `LegalTrace` premise is hidden: the trace is produced,
not assumed.
-/
import Rho5.Shared.MinorGrowthThreshold
import Rho5.Shared.MinorCPDomain
import Rho5.Shared.BottomRightVariation
import Rho5.Shared.GrowthSupremum

namespace Rho5.GlobalMinorReduction

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r)

/-- D62's scalar abbreviations coincide with D67's minors (same definitions, two names).
Recorded so downstream can move between the finite domain and the threshold statement
without ambiguity. -/
theorem B_eq_d62 (M : Matrix5) :
    Rho5.MinorGrowthThreshold.B M = Rho5.MinorCPDomain.B M := rfl

/-- The `C` bridge, as for `B`. -/
theorem C_eq_d62 (M : Matrix5) :
    Rho5.MinorGrowthThreshold.C M = Rho5.MinorCPDomain.C M := rfl

/-- **The actual trace of a `PolyCP` matrix.**  This is the existence statement the
forward direction rests on: the frame gives D55's nine qualifications, feasibility at
`0` is D55's `L ≤ 0 ≤ U`, and the shift-`0` trace is a trace of `M` itself. -/
theorem legalTrace_five (M : Matrix5) (h00 : M 0 0 = 1)
    (hpoly : Rho5.MinorCPDomain.PolyCP M) :
    Rho5.CompletePivotPath.LegalTrace M
      [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|] := by
  obtain ⟨hmax, hcp0, hcp4, hcp3, hcp2, hp, hk, hr⟩ :=
    (Rho5.MinorCPDomain.polyCP_iff_frame M h00).mp hpoly
  have hLU := Rho5.BottomRightVariation.L_le_zero_le_U M hmax h00 hcp0 hcp4 hcp3 hcp2 hp hk hr
  have hfeas : Rho5.BottomRightVariation.Feasible M 0 :=
    (Rho5.BottomRightVariation.feasible_iff_interval M 0).mpr ⟨hLU.1, hLU.2⟩
  have htrace :=
    Rho5.BottomRightVariation.legalTrace_shift M 0 hmax h00 hcp0 hcp4 hcp3 hcp2 hp hk hr hfeas
  rw [Rho5.BottomRightVariation.shift_zero] at htrace
  have hvals : Rho5.BottomRightVariation.traceValues M 0
      = [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|] := by
    simp [Rho5.BottomRightVariation.traceValues]
  rwa [hvals] at htrace

/-- **Forward direction.**  A global bound `rho5Trace ≤ T` forces both polynomial
inequalities on every actual `PolyCP` matrix. -/
theorem inequalities_of_rho5Trace_le {T : ℝ} (hT : 4 ≤ T)
    (hrho : Rho5.GrowthSupremum.rho5Trace ≤ T) :
    ∀ M : Matrix5, M 0 0 = 1 → Rho5.MinorCPDomain.PolyCP M →
      (Rho5.MinorGrowthThreshold.C M ≤ T * Rho5.MinorGrowthThreshold.B M ∧
        |M.det| ≤ T * Rho5.MinorGrowthThreshold.C M) := by
  intro M h00 hpoly
  obtain ⟨hmax, hcp0, hcp4, hcp3, -, hp, hk, hr⟩ :=
    (Rho5.MinorCPDomain.polyCP_iff_frame M h00).mp hpoly
  have htrace := legalTrace_five M h00 hpoly
  have hMne : M ≠ 0 := by
    intro hzero
    rw [hzero] at h00
    norm_num at h00
  have hmem : Rho5.GrowthModel.growthRatio M
      [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|]
        ∈ Rho5.GrowthModel.GrowthValues :=
    ⟨M, _, hMne, htrace, rfl⟩
  have hle : Rho5.GrowthModel.growthRatio M
      [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|] ≤ T :=
    (Rho5.GrowthSupremum.le_rho5Trace hmem).trans hrho
  exact (Rho5.MinorGrowthThreshold.threshold_iff hmax h00 hcp0 hcp4 hcp3 hp hk hr hT).mp hle

end Rho5.GlobalMinorReduction
