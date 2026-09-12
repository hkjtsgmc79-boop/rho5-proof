import Rho5.ExternalFourthPivot.Transport
import Rho5.Shared.CanonicalTail.TailValues
import Rho5.Shared.NestedThreePivot.StageB

/-!
# D86 applied to a single arbitrary normalized trace

The low-peak branch uses only list semantics. The high-peak branch derives every
`PolyCP` premise from the *same* actual positive-leading trace. No full-length or
positive-prefix assumption is exposed at the arbitrary-path endpoint.
-/
namespace Rho5.ExternalFourthPivot

open Rho5
open Rho5.Certificate.B24Extraction (p k r)

/-- High peak makes this same normalized leading matrix a genuine PolyCP matrix. -/
theorem polyCP_of_positive_leading_high_peak
    (M : Matrix5) (values : List ℝ) (hmax : matrixEntryMax M = 1)
    (h00 : M 0 0 = 1) (htrace : LeadingSigns.LeadingTracePos M values)
    (hpeak : 4 < GrowthModel.tracePeak values) : MinorCPDomain.PolyCP M := by
  have hgrowth : 4 < GrowthModel.growthRatio M values := by
    rw [GrowthModel.growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one hmax]
    exact hpeak
  obtain ⟨h0, h1, h2, h3, _, hp, hk, hr, _, _⟩ :=
    CanonicalTail.prefix_structure hmax h00 htrace hgrowth
  exact (MinorCPDomain.polyCP_iff_frame M h00).mpr
    ⟨hmax, h0, h1, h2, h3, hp, hk, hr⟩

/-- A leading positive-prefix trace: D86 supplies the only new numerical estimate. -/
theorem positive_leading_fourth_le_four
    (M : Matrix5) (values : List ℝ) (hmax : matrixEntryMax M = 1)
    (h00 : M 0 0 = 1) (htrace : LeadingSigns.LeadingTracePos M values) :
    values.getD 3 0 ≤ 4 := by
  by_cases hsmall : GrowthModel.tracePeak values ≤ 4
  · exact (getD_le_tracePeak values 3).trans hsmall
  · have hpeak : 4 < GrowthModel.tracePeak values := lt_of_not_ge hsmall
    have hP : MinorCPDomain.PolyCP M :=
      polyCP_of_positive_leading_high_peak M values hmax h00 htrace hpeak
    have hgrowth : 4 < GrowthModel.growthRatio M values := by
      rw [GrowthModel.growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one hmax]
      exact hpeak
    have hvalues : values = [1, p M, k M, r M, |CanonicalTail.delta M|] :=
      (CanonicalTail.values_eq_five hmax h00 htrace hgrowth).1
    rw [hvalues]
    simpa only [List.getD_cons_succ, List.getD_cons_zero]
      using NestedThreePivot.fourth_pivot_le_four M h00 hP

/-- Arbitrary normalized original matrix and arbitrary legal path, including ties/stops. -/
theorem normalized_fourth_pivot_le_four
    (A : Matrix5) (values : List ℝ) (hmax : matrixEntryMax A = 1)
    (htrace : CompletePivotPath.LegalTrace A values) : values.getD 3 0 ≤ 4 := by
  obtain ⟨M, hMmax, hM00, hpositive⟩ :=
    exists_normalized_positive_matrix A values hmax htrace
  exact positive_leading_fourth_le_four M values hMmax hM00 hpositive

end Rho5.ExternalFourthPivot
