import Rho5.Shared.BNormalizationInterface.Defs
import Rho5.ExternalTailSaturation.Classification

/-!
# D130 — what a proper-B representative already pays, and what it does not

Every field of `Qualified (extract M)` is *paid* for a proper-B representative by theorems that
already exist, with their hypotheses discharged from `LeadingInput`/`ProperB`:

| `Qualified` field | paying theorem | hypotheses discharged by |
|---|---|---|
| `physical` | `B24Extraction.physical_extract` | `LeadingInput` (`head`, `cp0..cp3`, `p_pos`, `k_pos`) + `ProperB.r_pos`, `ProperB.w_eq` |
| `headBand` | `B24Extraction.headBand_extract` | `LeadingInput.head`, `cp0`, `cp1`, `p_pos` |
| `p_pos` | `B24Extraction.p_extract` | `LeadingInput.p_pos` |
| `k_pos` | `B24Extraction.extract_zero` | `LeadingInput.k_pos` |
| `s_nonneg` | `B24Extraction.extract_two` | `ProperB.s_pos` |
| `s_le_r` | `B24Extraction.extract_two`, `extract_one` | `ProperB.s_lt` |
| `t_nonneg` | `B24Extraction.extract_three` | `ProperB.t_pos` |

The three remaining `NormalizedB` conditions are **not** paid and are therefore kept as the
explicit `ResidualGap` hypothesis; `normalizedB_iff_residualGap` proves they are exactly the
residual (nothing is hidden and nothing is assumed twice).
-/

noncomputable section

namespace Rho5.Shared.BNormalizationInterface

open Rho5 (Matrix5)
open Rho5.Certificate.B16 (Point Physical)
open Rho5.Certificate.B24Extraction (extract p k r s t)
open Rho5.Certificate.B24MinorBridge (Qualified)
open Rho5.Certificate.B24Reconstruction (HeadBand)
open Rho5.ExternalTailSaturation (LeadingInput ProperB DClassification)
open Rho5.ExternalBFibreCapacity (NormalizedB)

/-! ## 1. The payable fields -/

/-- The head band of the extracted point, from the leading input alone.  The four hypotheses of
`headBand_extract` are exactly `LeadingInput.head`, `cp0`, `cp1`, `p_pos`. -/
theorem headBand_extract_of_leadingInput {M : Matrix5} (h : LeadingInput M) :
    HeadBand (extract M) :=
  Rho5.Certificate.B24Extraction.headBand_extract M h.head h.cp0 h.cp1 h.p_pos

/-- The physical layer of the extracted point.  `physical_extract` additionally needs
`T2 M 1 1 = -r M`, which is exactly `ProperB.w_eq` because `w M` *is* `T2 M 1 1`, plus
`0 < r M`, which is `ProperB.r_pos`. -/
theorem physical_extract_of_properB {M : Matrix5} (h : LeadingInput M) (hb : ProperB M) :
    Physical (extract M) :=
  Rho5.Certificate.B24Extraction.physical_extract M h.head (ne_of_gt h.p_pos)
    (ne_of_gt h.k_pos) hb.w_eq h.cp0 h.cp1 h.cp2 h.cp3 h.p_pos h.k_pos hb.r_pos

/-- **All seven `Qualified` fields for a proper-B representative.**  This is the part of the
bridge that existing theorems already pay; no extra hypothesis beyond the two inputs is used. -/
theorem qualified_extract_of_properB {M : Matrix5} (h : LeadingInput M) (hb : ProperB M) :
    Qualified (extract M) where
  physical := physical_extract_of_properB h hb
  headBand := headBand_extract_of_leadingInput h
  p_pos := by
    rw [Rho5.Certificate.B24Extraction.p_extract]
    exact h.p_pos
  k_pos := by
    rw [Rho5.Certificate.B24Extraction.extract_zero]
    exact h.k_pos
  s_nonneg := by
    rw [Rho5.Certificate.B24Extraction.extract_two]
    exact le_of_lt hb.s_pos
  s_le_r := by
    rw [Rho5.Certificate.B24Extraction.extract_two, Rho5.Certificate.B24Extraction.extract_one]
    exact le_of_lt hb.s_lt
  t_nonneg := by
    rw [Rho5.Certificate.B24Extraction.extract_three]
    exact le_of_lt hb.t_pos

/-! ## 2. The residual, and the conditional bridge -/

/-- The residual is *necessary*: any `NormalizedB (extract M)` already contains it. -/
theorem residualGap_of_normalizedB {M : Matrix5} (h : NormalizedB (extract M)) :
    ResidualGap M := by
  have h8 := h.2.1
  have h9 := h.2.2.1
  have h10 := h.2.2.2
  rw [Rho5.Certificate.B24Extraction.extract_eight] at h8
  rw [Rho5.Certificate.B24Extraction.extract_nine] at h9
  rw [Rho5.Certificate.B24Extraction.extract_ten] at h10
  exact ⟨h8, neg_nonneg.mp h9, h10⟩

/-- **The bridge, with the whole gap in the open.**  A proper-B representative whose corner signs
and fifth pivot satisfy the residual conditions is a `NormalizedB` point.  No condition is
hidden: the hypotheses are exactly `LeadingInput`, `ProperB` and `ResidualGap`. -/
theorem normalizedB_of_properB {M : Matrix5} (h : LeadingInput M) (hb : ProperB M)
    (hr : ResidualGap M) : NormalizedB (extract M) := by
  refine ⟨qualified_extract_of_properB h hb, ?_, ?_, ?_⟩
  · rw [Rho5.Certificate.B24Extraction.extract_eight]; exact hr.1
  · rw [Rho5.Certificate.B24Extraction.extract_nine]; exact neg_nonneg.mpr hr.2.1
  · rw [Rho5.Certificate.B24Extraction.extract_ten]; exact hr.2.2

/-- **Exactness.**  For a proper-B representative the residual conditions are not merely
sufficient — they are equivalent to the three conditions `NormalizedB` adds to `Qualified`.
So no existing theorem can pay them unless it concludes one of them, and no weaker set of
conditions can replace them. -/
theorem normalizedB_iff_residualGap {M : Matrix5} (h : LeadingInput M) (hb : ProperB M) :
    NormalizedB (extract M) ↔ ResidualGap M :=
  ⟨residualGap_of_normalizedB, normalizedB_of_properB h hb⟩

/-! ## 3. The D123 exit, consumed directly -/

/-- A `DClassification` exit in its proper-B branch gives the leading input for free, so the
conditional bridge applies to the classification's *real* representative `N` (an actual
`columnTie`/`rowTie`/identity image of `M`, not a new model): the only thing left to supply is
`ResidualGap N`. -/
theorem normalizedB_of_classification {M N : Matrix5} (d : DClassification M N)
    (hb : ProperB N) (hr : ResidualGap N) : NormalizedB (extract N) :=
  normalizedB_of_properB d.input hb hr

/-- The same statement with the residual made necessary as well: at a classification exit the
tail layer's `NormalizedB` hypothesis is *equivalent* to the two corner signs plus `1 ≤ p N`. -/
theorem classification_normalizedB_iff {M N : Matrix5} (d : DClassification M N)
    (hb : ProperB N) : NormalizedB (extract N) ↔ ResidualGap N :=
  normalizedB_iff_residualGap d.input hb

end Rho5.Shared.BNormalizationInterface
