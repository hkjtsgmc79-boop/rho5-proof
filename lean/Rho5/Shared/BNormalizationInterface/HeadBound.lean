import Rho5.Shared.BNormalizationInterface.Bridge
import Mathlib.Tactic.Linarith

/-!
# D130 — the paper route: `F > 4` forces `p > 1`, the head band forces `e * beta > 0`

`rho5_manuscript.tex` §`Exact reduction of the negative diagonal domain` (lines 611-647) proves,
for a complete source,

* `F ≤ 4 p`  (`cor:firstfour`, eq. `eq:F4p`), hence **`F > 4` requires `p > 1`**;
* the head bound then gives **`e * beta ≥ p - 1 > 0`**;
* a simultaneous sign flip of the second row and column makes `e, beta > 0`.

This module formalizes the two consequences that need no new matrix algebra: `p > 1` from the
paper's `F ≤ 4 p` input, `e * beta ≥ p - 1` from the `HeadBand` field already paid by
`qualified_extract_of_properB`, and the resulting dichotomy.  If `e` and `beta` already have the
required sign the extracted point *is* `NormalizedB`; otherwise they are both negative and the
paper's simultaneous second-row/column flip is the remaining step — the disjunction below is
exactly that fork, with no condition hidden and none assumed twice.

`F ≤ 4 p` is *paper-complete* mathematics; it is not yet a Lean theorem in the trees this lane may
import, so it enters as the explicitly named hypothesis `hFp` instead of being assumed silently.
-/

noncomputable section

namespace Rho5.Shared.BNormalizationInterface

open Rho5 (Matrix5)
open Rho5.Certificate.B16 (Point Physical)
open Rho5.Certificate.B24Extraction (extract p k r s t F)
open Rho5.Certificate.B24MinorBridge (Qualified)
open Rho5.Certificate.B24Reconstruction (HeadBand e beta)
open Rho5.ExternalTailSaturation (LeadingInput ProperB)
open Rho5.ExternalBFibreCapacity (NormalizedB)

/-- **The head bound, read as a lower bound on `e * beta`.**  From the already-paid `HeadBand`
field of the extracted point: `p - 1 ≤ e * beta`. -/
theorem e_mul_beta_ge {M : Matrix5} (h : LeadingInput M) (hb : ProperB M) :
    p M - 1 ≤ e (extract M) * beta (extract M) := by
  have hhead := (qualified_extract_of_properB h hb).headBand.abs_p_sub_e_mul_beta
  rw [Rho5.Certificate.B24Extraction.p_extract] at hhead
  have h1 := (abs_le.mp hhead).2
  linarith

/-- **`F > 4` forces `p > 1`**, via the paper's `cor:firstfour` bound `F ≤ 4 p`. -/
theorem one_lt_p_of_four_lt_F {M : Matrix5} (hF : 4 < F M) (hFp : F M ≤ 4 * p M) :
    1 < p M := by
  linarith

/-- **`e * beta > 0` on the high-value branch.**  Combines `1 < p` (paper route) with the head
bound `p - 1 ≤ e * beta`; this is the step that makes the two corner signs agree. -/
theorem e_mul_beta_pos_of_four_lt_F {M : Matrix5} (h : LeadingInput M) (hb : ProperB M)
    (hF : 4 < F M) (hFp : F M ≤ 4 * p M) :
    0 < e (extract M) * beta (extract M) := by
  have hp := one_lt_p_of_four_lt_F hF hFp
  have hge := e_mul_beta_ge h hb
  linarith

/-- **The fork.**  On the high-value branch the extracted point is either already `NormalizedB`
(both corner signs correct) or both corner entries are strictly negative — the exact situation
the paper resolves by the simultaneous sign flip of the second row and column.  Nothing else can
happen, because `ProperB` already pays every `Qualified` field. -/
theorem normalizedB_or_bothNegative {M : Matrix5} (h : LeadingInput M) (hb : ProperB M)
    (hF : 4 < F M) (hFp : F M ≤ 4 * p M) :
    NormalizedB (extract M) ∨ (e (extract M) < 0 ∧ beta (extract M) < 0) := by
  have hp := one_lt_p_of_four_lt_F hF hFp
  have hq := qualified_extract_of_properB h hb
  have hpos := e_mul_beta_pos_of_four_lt_F h hb hF hFp
  rcases mul_pos_iff.mp hpos with ⟨he, hbe⟩ | ⟨he, hbe⟩
  · left
    refine ⟨hq, ?_, ?_, ?_⟩
    · rw [Rho5.Certificate.B24Extraction.extract_eight]
      exact le_of_lt hp
    · have he' : 0 ≤ -M 0 1 := by
        rw [Rho5.Certificate.B24Extraction.e_extract] at he
        exact le_of_lt he
      rw [Rho5.Certificate.B24Extraction.extract_nine]
      exact he'
    · have hbe' : 0 ≤ M 1 0 := by
        rw [Rho5.Certificate.B24Extraction.beta_extract] at hbe
        exact le_of_lt hbe
      rw [Rho5.Certificate.B24Extraction.extract_ten]
      exact hbe'
  · exact Or.inr ⟨he, hbe⟩

/-- The same fork at the D123 classification exit: the tail layer's `ProperB` branch with the
high value `F > 4` is `NormalizedB` up to the corner-sign fork only. -/
theorem classification_normalizedB_or_bothNegative {M N : Matrix5}
    (d : Rho5.ExternalTailSaturation.DClassification M N) (hb : ProperB N)
    (hF : 4 < F N) (hFp : F N ≤ 4 * p N) :
    NormalizedB (extract N) ∨ (e (extract N) < 0 ∧ beta (extract N) < 0) :=
  normalizedB_or_bothNegative d.input hb hF hFp

end Rho5.Shared.BNormalizationInterface
