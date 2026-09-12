/-
D65 — item 2: on the balanced branch the growth ratio is the B24 height
=======================================================================

Given an actual `Matrix5 M` with `matrixEntryMax M = 1` and an actual trace whose five values
are `[1, p M, k M, r M, |delta M|]`, a growth ratio `> 4` forces the fifth value to be the
maximum of the list, hence (by item 1) `growthRatio = F M`.

The fifth value's maximality is **proved**, not assumed: `1`, `p`, `k` are bounded by the paid
D58 package (`p ≤ 2`, `k ≤ 4`), `r ≤ F` by item 1, and the list maximum exceeds `4`, so nothing
except `F` can attain it.
-/
import Rho5.Certificate.BalancedMaximizer.Height
import Rho5.Shared.HighGrowthMargins

namespace Rho5.Certificate.BalancedMaximizer

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)

/-- The five-value trace used throughout this file. -/
noncomputable def balancedValues (M : Matrix5) : List ℝ :=
  [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|]

/-- **Auxiliary bound.**  On the balanced branch every value of the five-term trace is at most
`max (F M) 4`, hence so is the peak.

`1` is below `4`; `p M ≤ 2` and `k M ≤ 4` come from the paid D58 high-growth package; `r M ≤ F M`
and `|delta M| = F M` are item 1. -/
theorem tracePeak_le_max_F_four (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M (balancedValues M))
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    Rho5.GrowthModel.tracePeak (balancedValues M) ≤ max (F M) 4 := by
  obtain ⟨hpmax, hkmax, -, -, -, -, hr2, -, -⟩ :=
    Rho5.HighGrowthMargins.high_growth_package hM h00 h hgrowth
  have hrpos : 0 < r M := lt_trans (by norm_num : (0 : ℝ) < 2) hr2
  have hFabs : |Rho5.CanonicalTail.delta M| = F M := abs_delta_eq_F M htail hrpos hs ht
  have hrF : r M ≤ F M := r_le_F M hrpos hs ht
  have hFnonneg : 0 ≤ F M := F_nonneg M hrpos hs ht
  have hbound4 : (4 : ℝ) ≤ max (F M) 4 := le_max_right _ _
  have hall : ∀ v ∈ balancedValues M, v ≤ max (F M) 4 := by
    intro v hv
    simp only [balancedValues, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact le_trans (by norm_num : (1 : ℝ) ≤ 4) hbound4
    · exact le_trans hpmax (le_trans (by norm_num : (2 : ℝ) ≤ 4) hbound4)
    · exact le_trans hkmax hbound4
    · exact le_trans hrF (le_max_left _ _)
    · rw [hFabs]; exact le_max_left _ _
  exact Rho5.GrowthModel.tracePeak_le (le_trans hFnonneg (le_max_left _ _)) hall

/-- **Auxiliary.**  On the balanced branch the height `F M` exceeds `4`: the peak is above `4`
and is at most `max (F M) 4`. -/
theorem four_lt_F (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M (balancedValues M))
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    (4 : ℝ) < F M := by
  have hgr : Rho5.GrowthModel.growthRatio M (balancedValues M)
      = Rho5.GrowthModel.tracePeak (balancedValues M) := by
    rw [Rho5.GrowthModel.growthRatio, hM, div_one]
  have hpeak4 : (4 : ℝ) < Rho5.GrowthModel.tracePeak (balancedValues M) := by
    rw [← hgr]; exact hgrowth
  have hlt : (4 : ℝ) < max (F M) 4 :=
    lt_of_lt_of_le hpeak4 (tracePeak_le_max_F_four M hM h00 h hgrowth htail hs ht)
  exact (lt_max_iff.mp hlt).resolve_right (lt_irrefl 4)

/-- **The ordering facts D37 consumes.**  On the balanced branch the B24 height dominates the
first four trace values, exactly the `h1`, `h2`, `h3`, `h4` inputs of
`B24Extraction.growthRatio_extract_eq`. -/
theorem order_le_F (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M (balancedValues M))
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    1 ≤ F M ∧ p M ≤ F M ∧ k M ≤ F M ∧ r M ≤ F M := by
  obtain ⟨hpmax, hkmax, -, -, -, -, hr2, -, -⟩ :=
    Rho5.HighGrowthMargins.high_growth_package hM h00 h hgrowth
  have hrpos : 0 < r M := lt_trans (by norm_num : (0 : ℝ) < 2) hr2
  have h4F : (4 : ℝ) < F M := four_lt_F M hM h00 h hgrowth htail hs ht
  exact ⟨le_trans (by norm_num : (1 : ℝ) ≤ 4) h4F.le,
         le_trans hpmax (le_trans (by norm_num : (2 : ℝ) ≤ 4) h4F.le),
         le_trans hkmax h4F.le,
         r_le_F M hrpos hs ht⟩

/-- **Item 2.**  On the balanced branch the growth ratio of the five-value trace is `F M`.

Hypotheses are exactly the actual-matrix ones the card lists plus the paid high-growth
package input (`LeadingTracePos` and `4 < growthRatio`), from which `p ≤ 2`, `k ≤ 4` and
`0 < r` are derived by D58; `s`, `t` are only assumed nonnegative. -/
theorem growthRatio_eq_F (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M (balancedValues M))
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    Rho5.GrowthModel.growthRatio M (balancedValues M) = F M := by
  obtain ⟨-, -, -, -, -, -, hr2, -, -⟩ :=
    Rho5.HighGrowthMargins.high_growth_package hM h00 h hgrowth
  have hrpos : 0 < r M := lt_trans (by norm_num : (0 : ℝ) < 2) hr2
  have hFabs : |Rho5.CanonicalTail.delta M| = F M := abs_delta_eq_F M htail hrpos hs ht
  -- the growth ratio is the trace peak, because the matrix is normalized
  have hgr : Rho5.GrowthModel.growthRatio M (balancedValues M)
      = Rho5.GrowthModel.tracePeak (balancedValues M) := by
    rw [Rho5.GrowthModel.growthRatio, hM, div_one]
  -- `F` is one of the values, hence below the peak
  have hmemF : F M ∈ balancedValues M := by
    simp only [balancedValues, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inr (Or.inr hFabs.symm)))
  have hFle : F M ≤ Rho5.GrowthModel.tracePeak (balancedValues M) :=
    Rho5.GrowthModel.le_tracePeak hmemF
  -- every value is at most `max (F M) 4`, and the peak exceeds `4`, so the maximum is `F M`
  have hpeakF : Rho5.GrowthModel.tracePeak (balancedValues M) ≤ F M := by
    have hbound := tracePeak_le_max_F_four M hM h00 h hgrowth htail hs ht
    rw [max_eq_left (four_lt_F M hM h00 h hgrowth htail hs ht).le] at hbound
    exact hbound
  rw [hgr, le_antisymm hpeakF hFle]

end Rho5.Certificate.BalancedMaximizer
