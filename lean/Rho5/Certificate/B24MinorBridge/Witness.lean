import Rho5.Certificate.B24MinorBridge.Minors
import Rho5.Shared.MinorCPDomain

/-!
# D71 / B24MinorBridge — qualified B24 points enter `PolyCP`, with the exact readings

The card's qualification list is packaged as the Prop-valued structure `Qualified z`:
`Physical z`, `HeadBand z`, `p z > 0`, `z 0 > 0`, `0 ≤ z 2`, `z 2 ≤ z 1`, `0 ≤ z 3`.
Nothing here asserts that such a `z` exists, and no G04 coordinate mapping is used.

From `Qualified z` this file derives:

* the actual frame of `M = reconstruct z` — `matrixEntryMax M = 1`, the four leading
  complete pivots on `M`/`S4 M`/`S3 M`/`T2 M`, and `p M, k M, r M > 0` — using only D28's
  and D33's paid pivot lemmas transported along `Schur.lean`, and hence `PolyCP M` through
  D62's `polyCP_iff_frame`;
* the actual D33 `LegalTrace` with the same list `[1, p z, z 0, z 1, z 23]`, the exact
  growth-ratio reading `growthRatio M […] = tracePeak […]`, the paid lower reading
  `z 23 ≤ growthRatio M […]`, and the exact value `growthRatio M […] = z 23` **only** under
  the explicit dominance hypotheses `1 ≤ z 23`, `p z ≤ z 23`, `z 0 ≤ z 23`, `z 1 ≤ z 23`.

`witness_bundle` collects exactly this data, so a future external B24 point can be fed in
without any hidden assumption on this side.
-/

namespace Rho5.Certificate.B24MinorBridge

open Rho5 (Matrix5)
open Rho5.Certificate.B16 (Point Physical D)
open Rho5.Certificate.B24Reconstruction (reconstruct firstStage HeadBand)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-! ## 1. The qualification package -/

/-- **The card's qualification list for a B24 point**, as a single `Prop`.  Every field is
an input fact; none of them is a conclusion, and no field asserts existence. -/
structure Qualified (z : Point) : Prop where
  /-- D33's physical-layer bounds. -/
  physical : Physical z
  /-- D28's head-band bounds (the fields `Physical` does not provide). -/
  headBand : HeadBand z
  /-- The second pivot is positive. -/
  p_pos : 0 < Rho5.Certificate.B24Reconstruction.p z
  /-- The first B24 coordinate is positive. -/
  k_pos : 0 < z 0
  /-- `s = z 2` is nonnegative. -/
  s_nonneg : 0 ≤ z 2
  /-- `s = z 2` is dominated by `r = z 1`. -/
  s_le_r : z 2 ≤ z 1
  /-- `t = z 3` is nonnegative. -/
  t_nonneg : 0 ≤ z 3

/-! ## 2. `PolyCP` for the reconstruction -/

/-- **The bridge.**  A qualified B24 point reconstructs to a matrix in D62's polynomial
domain: `PolyCP (reconstruct z)`. -/
theorem polyCP_reconstruct (z : Point) (h : Qualified z) :
    Rho5.MinorCPDomain.PolyCP (reconstruct z) := by
  have h00 : reconstruct z 0 0 = 1 :=
    Rho5.Certificate.B24Reconstruction.reconstruct_zero_zero z
  refine (Rho5.MinorCPDomain.polyCP_iff_frame (reconstruct z) h00).mpr
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Rho5.Certificate.B24Reconstruction.matrixEntryMax_reconstruct z h.physical h.headBand
  · exact Rho5.Certificate.B24Reconstruction.isCompletePivot_reconstruct_zero_zero z h.physical
      h.headBand
  · rw [S4_reconstruct]
    exact Rho5.Certificate.B24Reconstruction.isCompletePivot_firstStage_of_physical z h.physical
      h.headBand h.p_pos
  · rw [S3_reconstruct z (ne_of_gt h.p_pos)]
    exact Rho5.Certificate.B24Trace.isCompletePivot_D_zero_zero z h.physical h.k_pos
  · rw [T2_reconstruct z (ne_of_gt h.p_pos) (ne_of_gt h.k_pos)]
    exact Rho5.Certificate.B24Trace.isCompletePivot_tail2_zero_zero z h.physical h.s_nonneg
      h.s_le_r h.t_nonneg
  · rw [p_reconstruct]; exact h.p_pos
  · rw [k_reconstruct z (ne_of_gt h.p_pos)]; exact h.k_pos
  · rw [r_reconstruct z (ne_of_gt h.p_pos) (ne_of_gt h.k_pos)]
    exact Rho5.Certificate.B24Reconstruction.r_pos h.physical

/-- The actual frame behind `polyCP_reconstruct`, stated explicitly. -/
theorem frame_reconstruct (z : Point) (h : Qualified z) :
    Rho5.matrixEntryMax (reconstruct z) = 1 ∧
      Rho5.Pivot.IsCompletePivot (reconstruct z) 0 0 ∧
      Rho5.Pivot.IsCompletePivot (S4 (reconstruct z)) 0 0 ∧
      Rho5.Pivot.IsCompletePivot (S3 (reconstruct z)) 0 0 ∧
      Rho5.Pivot.IsCompletePivot (T2 (reconstruct z)) 0 0 ∧
      0 < p (reconstruct z) ∧ 0 < k (reconstruct z) ∧ 0 < r (reconstruct z) :=
  ((Rho5.MinorCPDomain.polyCP_iff_frame (reconstruct z)
    (Rho5.Certificate.B24Reconstruction.reconstruct_zero_zero z)).mp
      (polyCP_reconstruct z h))

/-! ## 3. The D33 trace and the growth readings -/

/-- **The actual D33 `LegalTrace`**, with the same value list as D33's paid theorem
(`p z = z 8` by `p_coord`). -/
theorem legalTrace_reconstruct (z : Point) (h : Qualified z) :
    Rho5.CompletePivotPath.LegalTrace (reconstruct z)
      [1, Rho5.Certificate.B24Reconstruction.p z, z 0, z 1, z 23] :=
  Rho5.Certificate.B24Trace.legalTrace_reconstruct z h.physical h.headBand h.p_pos h.k_pos
    h.s_nonneg h.s_le_r h.t_nonneg

/-- The growth ratio of the reconstruction is the `tracePeak` of that list. -/
theorem growthRatio_reconstruct (z : Point) (h : Qualified z) :
    Rho5.GrowthModel.growthRatio (reconstruct z)
        [1, Rho5.Certificate.B24Reconstruction.p z, z 0, z 1, z 23] =
      Rho5.GrowthModel.tracePeak [1, Rho5.Certificate.B24Reconstruction.p z, z 0, z 1, z 23] :=
  Rho5.Certificate.B24Trace.growthRatio_reconstruct z h.physical h.headBand

/-- **The paid lower reading**: `z 23` never exceeds the actual growth ratio. -/
theorem le_growthRatio_z23 (z : Point) (h : Qualified z) :
    z 23 ≤ Rho5.GrowthModel.growthRatio (reconstruct z)
      [1, Rho5.Certificate.B24Reconstruction.p z, z 0, z 1, z 23] :=
  Rho5.Certificate.B24Trace.le_growthRatio_z23 z h.physical h.headBand

/-- **The exact realization at `z 23`**, available *only* with the four explicit dominance
hypotheses `1 ≤ z 23`, `p z ≤ z 23`, `z 0 ≤ z 23`, `z 1 ≤ z 23` (a future external witness
must supply them; this lane does not assume they hold). -/
theorem growthRatio_eq_z23 (z : Point) (h : Qualified z)
    (h1 : 1 ≤ z 23) (h2 : Rho5.Certificate.B24Reconstruction.p z ≤ z 23) (h3 : z 0 ≤ z 23)
    (h4 : z 1 ≤ z 23) :
    Rho5.GrowthModel.growthRatio (reconstruct z)
      [1, Rho5.Certificate.B24Reconstruction.p z, z 0, z 1, z 23] = z 23 :=
  Rho5.Certificate.B24Trace.growthRatio_eq_z23 z h.physical h.headBand h1 h2 h3 h4

/-! ## 4. The packaged witness data -/

/-- **Attainment-ready witness bundle** (no existence claim): for any *given* qualified
B24 point, the polynomial domain, the four exact minor readings, the actual legal trace
and the paid lower growth reading all hold at once. -/
theorem witness_bundle (z : Point) (h : Qualified z) :
    Rho5.MinorCPDomain.PolyCP (reconstruct z) ∧
      (Rho5.MinorGrowthThreshold.A (reconstruct z) = z 8 ∧
        Rho5.MinorGrowthThreshold.B (reconstruct z) = z 8 * z 0 ∧
        Rho5.MinorGrowthThreshold.C (reconstruct z) = z 8 * z 0 * z 1 ∧
        Rho5.MinorGrowthThreshold.D (reconstruct z) = -z 8 * z 0 * z 1 * z 23) ∧
      Rho5.CompletePivotPath.LegalTrace (reconstruct z)
        [1, Rho5.Certificate.B24Reconstruction.p z, z 0, z 1, z 23] ∧
      z 23 ≤ Rho5.GrowthModel.growthRatio (reconstruct z)
        [1, Rho5.Certificate.B24Reconstruction.p z, z 0, z 1, z 23] :=
  ⟨polyCP_reconstruct z h,
    ⟨A_reconstruct z, B_reconstruct z h.p_pos, C_reconstruct z h.p_pos h.k_pos,
      D_reconstruct z h.physical h.p_pos h.k_pos⟩,
    legalTrace_reconstruct z h,
    le_growthRatio_z23 z h⟩

end Rho5.Certificate.B24MinorBridge
