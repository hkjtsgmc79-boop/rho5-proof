/-
D67 — the actual growth threshold as two polynomial minor inequalities.

For an actual normalized matrix (`matrixEntryMax M = 1`, `M 0 0 = 1`) with the first
three leading complete pivots and `p, k, r > 0`, and any threshold `T ≥ 4`:

    growthRatio M [1, p M, k M, r M, |delta M|] ≤ T
        ↔  C M ≤ T * B M  ∧  |D M| ≤ T * C M

where `A/B/C/D` are the actual signed original-matrix minors of
`MinorGrowthThreshold/Defs.lean`.  In words: the growth threshold is *exactly* the
conjunction of the two polynomial minor inequalities `p*k*r ≤ T*p*k` and
`|det M| ≤ T*p*k*r`.

The equivalence is proved from the two readings `r = C/B` and `delta = D/C` with
positive denominators, the normalized peak (`matrixEntryMax M = 1`, so the growth ratio
is the trace peak itself), and the paid one-step upper bounds `p ≤ 2`, `k ≤ 4` (D58's
`upper_bounds`, whose hypotheses are the three complete pivots and `p, k > 0`).

**No `4 < growth` premise appears in the threshold equivalence**, and no full-rank,
sign-of-`det`, or determinant-nonvanishing premise is assumed: the determinant-zero
case is carried through `|D| = |delta| * C` and is not excluded anywhere.  The fourth
leading complete pivot (`T2 M`) is part of the actual domain but is not needed here.

`T ≥ 4` is used only to absorb `p` and `k` into the threshold (`p ≤ 2 ≤ T`,
`k ≤ 4 ≤ T`, `1 ≤ T`); it is an explicit hypothesis, not a hidden one.
-/
import Rho5.Shared.MinorGrowthThreshold.Defs
import Mathlib.Tactic.Linarith

namespace Rho5.MinorGrowthThreshold

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **The threshold equivalence.**  The actual five-value growth ratio is at most `T`
exactly when both polynomial minor inequalities hold. -/
theorem threshold_iff {M : Matrix5} {T : ℝ}
    (hmax : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp0 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) (hT : 4 ≤ T) :
    Rho5.GrowthModel.growthRatio M [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|] ≤ T ↔
      C M ≤ T * B M ∧ |D M| ≤ T * C M := by
  have hg : Rho5.GrowthModel.growthRatio M [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|]
      = Rho5.GrowthModel.tracePeak [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|] := by
    rw [Rho5.GrowthModel.growthRatio_eq, hmax, div_one]
  have hB : 0 < B M := B_pos M h00 hp hk
  have hC : 0 < C M := C_pos M h00 hp hk hr
  obtain ⟨hp2, hk4, -⟩ := Rho5.HighGrowthMargins.upper_bounds M h00 hcp0 hcp4 hcp3 hp hk
  rw [hg]
  constructor
  · -- ⟹ : the two minor inequalities
    intro hle
    have hrT : r M ≤ T :=
      (Rho5.GrowthModel.le_tracePeak (by simp)).trans hle
    have hdT : |Rho5.CanonicalTail.delta M| ≤ T :=
      (Rho5.GrowthModel.le_tracePeak (by simp)).trans hle
    refine ⟨?_, ?_⟩
    · rw [C_eq_r_mul_B M h00 hp hk]
      exact mul_le_mul_of_nonneg_right hrT (le_of_lt hB)
    · rw [abs_D_eq_abs_delta_mul_C M h00 hp hk hr]
      exact mul_le_mul_of_nonneg_right hdT (le_of_lt hC)
  · -- ⟸ : every trace value is at most `T`
    rintro ⟨hCB, hDC⟩
    refine Rho5.GrowthModel.tracePeak_le (by linarith) ?_
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · linarith
    · linarith
    · linarith
    · have h := hCB
      rw [C_eq_r_mul_B M h00 hp hk] at h
      exact le_of_mul_le_mul_right h hB
    · have h := hDC
      rw [abs_D_eq_abs_delta_mul_C M h00 hp hk hr] at h
      exact le_of_mul_le_mul_right h hC

/-- **The strict-violation form.**  Negating the threshold equivalence: a threshold `T`
is strictly below the actual growth ratio exactly when one of the two polynomial
inequalities fails strictly. -/
theorem threshold_lt_iff {M : Matrix5} {T : ℝ}
    (hmax : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp0 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) (hT : 4 ≤ T) :
    T < Rho5.GrowthModel.growthRatio M [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|] ↔
      T * B M < C M ∨ T * C M < |D M| := by
  have h := threshold_iff hmax h00 hcp0 hcp4 hcp3 hp hk hr hT
  constructor
  · intro hlt
    by_contra hcon
    have hc : C M ≤ T * B M ∧ |D M| ≤ T * C M := by
      obtain ⟨h1, h2⟩ := not_or.mp hcon
      exact ⟨not_lt.mp h1, not_lt.mp h2⟩
    exact absurd (h.mpr hc) (not_le.mpr hlt)
  · intro hcases
    by_contra hcon
    have hle : Rho5.GrowthModel.growthRatio M
        [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|] ≤ T := not_lt.mp hcon
    have hc := h.mp hle
    rcases hcases with h1 | h1
    · exact absurd hc.1 (not_le.mpr h1)
    · exact absurd hc.2 (not_le.mpr h1)

/-- **Signed-determinant corollary (`det M ≤ 0`).**  When the actual determinant is
nonpositive its absolute value is `-D M`, so the second minor inequality reads
`-D M ≤ T * C M`.  This is a named conditional corollary only; no sign of `D M` is
assumed by the main equivalence. -/
theorem threshold_iff_of_det_nonpos {M : Matrix5} {T : ℝ}
    (hmax : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp0 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) (hT : 4 ≤ T) (hD : M.det ≤ 0) :
    Rho5.GrowthModel.growthRatio M [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|] ≤ T ↔
      C M ≤ T * B M ∧ -D M ≤ T * C M := by
  have habs : |D M| = -D M := by
    rw [D]; exact abs_of_nonpos hD
  rw [threshold_iff hmax h00 hcp0 hcp4 hcp3 hp hk hr hT, habs]

end Rho5.MinorGrowthThreshold
