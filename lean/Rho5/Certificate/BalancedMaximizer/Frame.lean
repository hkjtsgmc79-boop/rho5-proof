/-
D65 — frame entry: the original card's four-CP positive prefix really does carry
`LeadingTracePos`, and the height / Physical / maximizer interfaces are consumed from it
=======================================================================================

The original card supplies an **actual normalized four-CP positive-prefix frame**
(`M 0 0 = 1`, four leading complete pivots, `p M > 0`, `k M > 0`, `r M > 0`) plus the balanced
condition `T2 M 1 1 = -r M` and `s M, t M ≥ 0`.  The first delivery consumed the extra premise
`LeadingSigns.LeadingTracePos M (balancedValues M)`; this module **removes** that premise by
building it from the frame, using the real constructors of the relation:

* the four leading steps are `LeadingTracePos.step` at `M`, `S4 M`, `S3 M`, `T2 M`, with pivots
  `M 0 0 = 1`, `p M`, `k M`, `r M` — all strictly positive, so no `zeroStop` can occur there;
* the final `1 × 1` block is `pivotSchur (T2 M) 0 0`, whose single entry is exactly
  `CanonicalTail.delta M` (D48 `delta_eq_pivotSchur`, itself D46
  `delta_eq_pivotSchur_zero_zero`).  The sign/magnitude of `delta M` is **free**: a zero pivot
  goes through `LeadingTracePos.zeroStop` (value `0 = |delta M|`), a nonzero pivot through
  `LeadingTracePos.lastStep` (value `|delta M|`, positivity *not* required).

**No full-rank assumption** is made and no fifth pivot is assumed nonzero; `1 × 1` legality of
the final pivot is D46's `isCompletePivot_fin_one` (proved there, not assumed here).

The frame-facing variants below (`frame_*`) are the card's height / Physical / maximizer
interfaces stated with the frame premises instead of a `LeadingTracePos` hypothesis, so no
downstream consumer has to discharge `LeadingTracePos` itself.

Not claimed here: existence of the frame, attainment or uniqueness of anything, the three
non-balanced boundary branches (`M44 = -1`, `S4_33 = -p`, `S3_22 = -k` stay open), and any
G04-to-matrix construction (D60's gap is untouched).
-/
import Mathlib.Tactic.FinCases
import Rho5.Certificate.BalancedMaximizer.Height
import Rho5.Certificate.BalancedMaximizer.GrowthValue
import Rho5.Certificate.BalancedMaximizer.Physical
import Rho5.Certificate.BalancedMaximizer.Maximizer
import Rho5.Shared.LeadingSigns
import Rho5.Shared.TailEnvelope
import Rho5.Shared.CanonicalTail

namespace Rho5.Certificate.BalancedMaximizer

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)

/-! ## 1. The frame's five-value trace is an actual `LeadingTracePos` -/

/-- The final `1 × 1` block after the three paid steps.  Its unique entry is `delta M`
(D48 `CanonicalTail.delta_eq_pivotSchur`), so the trace ends with `|delta M|`.  The two
constructor cases are the content of "the last pivot need not be positive":

* `delta M = 0` → the block is the zero matrix, hence `zeroStop` with value `0 = |delta M|`;
* `delta M ≠ 0` → `lastStep`, which requires legality and nonzeroness only. -/
private theorem leadingTracePos_lastBlock (M : Matrix5) :
    Rho5.LeadingSigns.LeadingTracePos (Rho5.PivotReindex.pivotSchur (T2 M) 0 0)
      [|Rho5.CanonicalTail.delta M|] := by
  by_cases hd : Rho5.CanonicalTail.delta M = 0
  · -- zero final pivot: `zeroStop` (no nonzero assumption)
    have hz : Rho5.PivotReindex.pivotSchur (T2 M) 0 0 = 0 := by
      funext i j
      fin_cases i
      fin_cases j
      simpa [Rho5.CanonicalTail.delta_eq_pivotSchur M] using hd
    have hle : Rho5.LeadingSigns.LeadingTracePos
        (Rho5.PivotReindex.pivotSchur (T2 M) 0 0) [0] :=
      Rho5.LeadingSigns.LeadingTracePos.zeroStop hz
    have habs : |Rho5.CanonicalTail.delta M| = (0 : ℝ) := by rw [hd, abs_zero]
    rw [habs]
    exact hle
  · -- nonzero final pivot: `lastStep`; the pivot is *not* claimed positive
    have hne : (Rho5.PivotReindex.pivotSchur (T2 M) 0 0) 0 0 ≠ 0 := by
      rwa [← Rho5.CanonicalTail.delta_eq_pivotSchur M]
    rw [Rho5.CanonicalTail.delta_eq_pivotSchur M]
    exact Rho5.LeadingSigns.LeadingTracePos.lastStep
      (Rho5.TailEnvelope.isCompletePivot_fin_one _) hne

/-- **The frame theorem (original card, no extra premise).**  From `M 0 0 = 1`, the four
leading complete pivots and `p M > 0`, `k M > 0`, `r M > 0`, the five-value prefix trace
`[1, p M, k M, r M, |delta M|]` is an actual `LeadingSigns.LeadingTracePos`.

No full-rank assumption, no `matrixEntryMax` and no `s`/`t` sign condition is used at this
stage; only the four leading pivots and `M 0 0 = 1` enter the `step` constructors. -/
theorem leadingTracePos_frame (M : Matrix5)
    (h00 : M 0 0 = 1)
    (hcp1 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp2 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) :
    Rho5.LeadingSigns.LeadingTracePos M [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|] := by
  have htail := leadingTracePos_lastBlock M
  -- level 2: pivot `T2 M 0 0 = r M`
  have h4 : Rho5.LeadingSigns.LeadingTracePos (T2 M)
      [r M, |Rho5.CanonicalTail.delta M|] :=
    Rho5.LeadingSigns.LeadingTracePos.step hcp4 (ne_of_gt hr) hr htail
  -- level 3: pivot `S3 M 0 0 = k M`
  have h3 : Rho5.LeadingSigns.LeadingTracePos (S3 M)
      [k M, r M, |Rho5.CanonicalTail.delta M|] :=
    Rho5.LeadingSigns.LeadingTracePos.step hcp3 (ne_of_gt hk) hk h4
  -- level 4: pivot `S4 M 0 0 = p M`
  have h2 : Rho5.LeadingSigns.LeadingTracePos (S4 M)
      [p M, k M, r M, |Rho5.CanonicalTail.delta M|] :=
    Rho5.LeadingSigns.LeadingTracePos.step hcp2 (ne_of_gt hp) hp h3
  -- level 5: pivot `M 0 0 = 1`
  have h1 : Rho5.LeadingSigns.LeadingTracePos M
      [M 0 0, p M, k M, r M, |Rho5.CanonicalTail.delta M|] :=
    Rho5.LeadingSigns.LeadingTracePos.step hcp1
      (by rw [h00]; norm_num) (by rw [h00]; norm_num) h2
  simpa only [h00] using h1

/-- The frame theorem in the `balancedValues` spelling used by items 2–4. -/
theorem leadingTracePos_balancedValues (M : Matrix5)
    (h00 : M 0 0 = 1)
    (hcp1 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp2 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) :
    Rho5.LeadingSigns.LeadingTracePos M (balancedValues M) := by
  simpa only [balancedValues] using
    leadingTracePos_frame M h00 hcp1 hcp2 hcp3 hcp4 hp hk hr

/-! ## 2. Frame-facing height interface (item 2 premises, no `LeadingTracePos` input) -/

/-- **Frame variant of the peak bound.** -/
theorem frame_tracePeak_le_max_F_four (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp1 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp2 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    Rho5.GrowthModel.tracePeak (balancedValues M) ≤ max (F M) 4 :=
  tracePeak_le_max_F_four M hM h00
    (leadingTracePos_balancedValues M h00 hcp1 hcp2 hcp3 hcp4 hp hk hr) hgrowth htail hs ht

/-- **Frame variant of `4 < F M`.** -/
theorem frame_four_lt_F (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp1 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp2 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    (4 : ℝ) < F M :=
  four_lt_F M hM h00
    (leadingTracePos_balancedValues M h00 hcp1 hcp2 hcp3 hcp4 hp hk hr) hgrowth htail hs ht

/-- **Frame variant of the ordering facts** D37's `growthRatio_extract_eq` consumes. -/
theorem frame_order_le_F (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp1 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp2 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    1 ≤ F M ∧ p M ≤ F M ∧ k M ≤ F M ∧ r M ≤ F M :=
  order_le_F M hM h00
    (leadingTracePos_balancedValues M h00 hcp1 hcp2 hcp3 hcp4 hp hk hr) hgrowth htail hs ht

/-- **Frame variant of item 2**: the growth value of the frame's actual trace is the B24
height. -/
theorem frame_growthRatio_eq_F (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp1 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp2 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    Rho5.GrowthModel.growthRatio M (balancedValues M) = F M :=
  growthRatio_eq_F M hM h00
    (leadingTracePos_balancedValues M h00 hcp1 hcp2 hcp3 hcp4 hp hk hr) hgrowth htail hs ht

/-! ## 3. Frame-facing Physical interface (item 3 premises) -/

/-- **Frame variant of item 3**: the explicit point `extract M` is physical, head-band,
reconstructs `M`, has B24 height coordinate equal to the actual growth value, and carries
the actual legal trace. -/
theorem frame_physical_point_at_height (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp1 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp2 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    Rho5.Certificate.B16.Physical (Rho5.Certificate.B24Extraction.extract M)
      ∧ Rho5.Certificate.B24Reconstruction.HeadBand (Rho5.Certificate.B24Extraction.extract M)
      ∧ Rho5.Certificate.B24Reconstruction.reconstruct (Rho5.Certificate.B24Extraction.extract M) = M
      ∧ (Rho5.Certificate.B24Extraction.extract M) 23
          = Rho5.GrowthModel.growthRatio M (balancedValues M)
      ∧ Rho5.CompletePivotPath.LegalTrace M [1, p M, k M, r M, F M] :=
  physical_point_at_height M hM h00
    (leadingTracePos_balancedValues M h00 hcp1 hcp2 hcp3 hcp4 hp hk hr) hgrowth htail hs ht

/-! ## 4. Frame-facing maximizer interface (item 4 premises) -/

/-- **Frame variant of the lower-bound membership.** -/
theorem frame_balanced_mem_growthValues (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp1 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp2 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    Rho5.GrowthModel.growthRatio M (balancedValues M) ∈ Rho5.GrowthModel.GrowthValues :=
  balanced_mem_growthValues M hM h00
    (leadingTracePos_balancedValues M h00 hcp1 hcp2 hcp3 hcp4 hp hk hr) hgrowth htail hs ht

/-- **Frame variant of item 4**: conditional on the actual global-maximizer equality
`g = rho5Trace`, the frame produces an explicit physical point at height `rho5Trace` that
reconstructs `M`, together with the global upper comparison.

The conditionality is unchanged and deliberate: the frame does **not** prove that a balanced
global maximizer exists or that its growth value saturates `rho5Trace`. -/
theorem frame_exists_physical_point_at_rho (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp1 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp2 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (hrho : Rho5.GrowthModel.growthRatio M (balancedValues M)
      = Rho5.GrowthSupremum.rho5Trace)
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    (∃ z, Rho5.Certificate.B16.Physical z
        ∧ Rho5.Certificate.B24Reconstruction.HeadBand z
        ∧ z 23 = Rho5.GrowthSupremum.rho5Trace
        ∧ Rho5.Certificate.B24Reconstruction.reconstruct z = M)
      ∧ ∀ g ∈ Rho5.GrowthModel.GrowthValues, g ≤ Rho5.GrowthSupremum.rho5Trace :=
  exists_physical_point_at_rho M hM h00
    (leadingTracePos_balancedValues M h00 hcp1 hcp2 hcp3 hcp4 hp hk hr) hgrowth hrho htail hs ht

end Rho5.Certificate.BalancedMaximizer
