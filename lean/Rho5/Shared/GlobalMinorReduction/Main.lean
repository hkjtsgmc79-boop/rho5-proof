/-
D69 — the reverse direction, the global equivalence, and the strict-violation form.

**Reverse.**  If `T < rho5Trace` (with `T ≥ 4`), D48's paid actual canonical witness
supplies an actual matrix `M` whose growth ratio *is* `rho5Trace` and which already
carries the whole frame; D62's `polyCP_iff_frame` then makes it a member of the finite
`PolyCP` domain, and D67's strict threshold form turns `T < growthRatio M […]` into a
violation of one of the two inequalities.  The witness is an attainment statement that
D48/D43 already paid for; nothing here assumes that an arbitrary low-growth matrix has a
positive prefix, and no attainment, full-rank or `LegalTrace` premise is hidden.

**Global equivalence.**  Combining the two directions gives, for every `T ≥ 4`:

    rho5Trace ≤ T  ↔  ∀ M, M 0 0 = 1 → PolyCP M → (C M ≤ T * B M ∧ |det M| ≤ T * C M)

which is the global coverage-to-finite-domain reduction.  The underlying inequalities at
alpha are *not* claimed.
-/
import Rho5.Shared.GlobalMinorReduction.Basic
import Rho5.Shared.CanonicalTail

namespace Rho5.GlobalMinorReduction

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r)

/-- **Reverse direction (counterexample form).**  Above a threshold `T ≥ 4`, a growth
ratio exceeding `T` is witnessed by an actual `PolyCP` matrix violating one of the two
polynomial inequalities. -/
theorem exists_counterexample_of_lt_rho5Trace {T : ℝ} (hT : 4 ≤ T)
    (hlt : T < Rho5.GrowthSupremum.rho5Trace) :
    ∃ M : Matrix5, M 0 0 = 1 ∧ Rho5.MinorCPDomain.PolyCP M ∧
      (T * Rho5.MinorGrowthThreshold.B M < Rho5.MinorGrowthThreshold.C M ∨
        T * Rho5.MinorGrowthThreshold.C M < |M.det|) := by
  have h4 : 4 < Rho5.GrowthSupremum.rho5Trace := lt_of_le_of_lt hT hlt
  obtain ⟨M, values, hmax, -, h00, -, hcp0, hcp4, hcp3, hcp2, hp, hk, hr,
    hvalues, -, hratio, -, -, -, -, -⟩ :=
    Rho5.CanonicalTail.exists_canonical_tail_witness h4
  refine ⟨M, h00, (Rho5.MinorCPDomain.polyCP_iff_frame M h00).mpr
    ⟨hmax, hcp0, hcp4, hcp3, hcp2, hp, hk, hr⟩, ?_⟩
  have hg : T < Rho5.GrowthModel.growthRatio M
      [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|] := by
    rw [← hvalues, hratio]
    exact hlt
  exact (Rho5.MinorGrowthThreshold.threshold_lt_iff hmax h00 hcp0 hcp4 hcp3 hp hk hr hT).mp hg

/-- **The global equivalence.**  For every threshold `T ≥ 4`, the global growth bound is
*exactly* the pair of polynomial minor inequalities on the actual finite `PolyCP`
domain. -/
theorem rho5Trace_le_iff_polyCP_inequalities {T : ℝ} (hT : 4 ≤ T) :
    Rho5.GrowthSupremum.rho5Trace ≤ T ↔
      ∀ M : Matrix5, M 0 0 = 1 → Rho5.MinorCPDomain.PolyCP M →
        (Rho5.MinorGrowthThreshold.C M ≤ T * Rho5.MinorGrowthThreshold.B M ∧
          |M.det| ≤ T * Rho5.MinorGrowthThreshold.C M) := by
  constructor
  · exact inequalities_of_rho5Trace_le hT
  · intro h
    by_contra hnot
    have hlt : T < Rho5.GrowthSupremum.rho5Trace := lt_of_not_ge hnot
    obtain ⟨M, h00, hpoly, hviol⟩ := exists_counterexample_of_lt_rho5Trace hT hlt
    rcases hviol with h1 | h1
    · exact absurd (h M h00 hpoly).1 (not_le.mpr h1)
    · exact absurd (h M h00 hpoly).2 (not_le.mpr h1)

/-- **Strict-violation form.**  Negating the global equivalence: `T` is strictly below the
global growth bound exactly when some actual `PolyCP` matrix violates one of the two
inequalities strictly. -/
theorem rho5Trace_lt_iff_exists {T : ℝ} (hT : 4 ≤ T) :
    T < Rho5.GrowthSupremum.rho5Trace ↔
      ∃ M : Matrix5, M 0 0 = 1 ∧ Rho5.MinorCPDomain.PolyCP M ∧
        (T * Rho5.MinorGrowthThreshold.B M < Rho5.MinorGrowthThreshold.C M ∨
          T * Rho5.MinorGrowthThreshold.C M < |M.det|) := by
  constructor
  · exact exists_counterexample_of_lt_rho5Trace hT
  · rintro ⟨M, h00, hpoly, hviol⟩
    by_contra hnot
    have hle : Rho5.GrowthSupremum.rho5Trace ≤ T := le_of_not_gt hnot
    have hc := inequalities_of_rho5Trace_le hT hle M h00 hpoly
    rcases hviol with h1 | h1
    · exact absurd hc.1 (not_le.mpr h1)
    · exact absurd hc.2 (not_le.mpr h1)

end Rho5.GlobalMinorReduction
