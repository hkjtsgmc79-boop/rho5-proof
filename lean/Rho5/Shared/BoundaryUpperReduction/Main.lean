/-
D74 — the reverse direction, the sorted-boundary global equivalence, and the
four-obligation certificate corollary.

**Reverse.**  If `T < rho5Trace` (with `T ≥ 4`), D68's accepted stage-A four-faces
existence gives an actual matrix `P` with `SortedBoundaryMaximizerFacts P values`,
`0 ≤ s P ≤ t P`, and all four saturated faces in Schur form.  D70's two paid bridges turn
those into D74's hypotheses — `tail_ordered_iff_minor_ordered_of_polyCP` converts the
sorted pair into the minor form `0 ≤ m4 P 0 1 ∧ m4 P 0 1 ≤ m4 P 1 0`, and
`boundaryFace_iff_schurFaces_of_polyCP` converts the Schur disjunction into
`BoundaryFace P` — while the record's frame gives `PolyCP P` through D62's
`polyCP_iff_frame`.  Since `growthRatio P values = rho5Trace > T` and `values` is the
five-value trace, D67's strict threshold form produces the violation.

**Certificate corollary.**  Conversely, an upper-bound proof on each of the four faces
separately — under the common feasible/sorted premises and `T ≥ 4` — suffices for the
global bound.  The corollary asserts none of the four inequalities, no alpha equality, no
`4 < rho5Trace` and no vanishing of the first three faces.

No balanced-maximum assumption and no extra full-rank premise is used anywhere; all four
faces are kept, and D70's own predicate is reused rather than replaced by a second
four-face framework.
-/
import Rho5.Shared.BoundaryUpperReduction.Forward

namespace Rho5.BoundaryUpperReduction

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **Reverse (counterexample form).**  Above a threshold `T ≥ 4`, a growth ratio
exceeding `T` is witnessed by an actual sorted boundary matrix violating one of the two
polynomial inequalities. -/
theorem exists_counterexample_of_lt_rho5Trace {T : ℝ} (hT : 4 ≤ T)
    (hlt : T < Rho5.GrowthSupremum.rho5Trace) :
    ∃ M : Matrix5, M 0 0 = 1 ∧ Rho5.MinorCPDomain.PolyCP M ∧
      0 ≤ Rho5.MinorCPDomain.m4 M 0 1 ∧
        Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 ∧
          Rho5.MinorBoundaryFaces.BoundaryFace M ∧
            (T * Rho5.MinorGrowthThreshold.B M < Rho5.MinorGrowthThreshold.C M ∨
              T * Rho5.MinorGrowthThreshold.C M < |M.det|) := by
  have h4 : 4 < Rho5.GrowthSupremum.rho5Trace := lt_of_le_of_lt hT hlt
  obtain ⟨P, values, hfacts, hs, hst, hbound⟩ :=
    Rho5.BoundaryMaximizer.exists_sorted_boundary_maximizer_four_faces h4
  have h00 : P 0 0 = 1 := hfacts.zero_zero
  have hpoly : Rho5.MinorCPDomain.PolyCP P :=
    (Rho5.MinorCPDomain.polyCP_iff_frame P h00).mpr
      ⟨hfacts.entryMax, hfacts.cp0, hfacts.cp4, hfacts.cp3, hfacts.cp2,
        hfacts.p_pos, hfacts.k_pos, hfacts.r_pos⟩
  have hminor : 0 ≤ Rho5.MinorCPDomain.m4 P 0 1 ∧
      Rho5.MinorCPDomain.m4 P 0 1 ≤ Rho5.MinorCPDomain.m4 P 1 0 :=
    (Rho5.MinorBoundaryFaces.tail_ordered_iff_minor_ordered_of_polyCP P h00 hpoly).mp
      ⟨hs, hst⟩
  have hface : Rho5.MinorBoundaryFaces.BoundaryFace P :=
    (Rho5.MinorBoundaryFaces.boundaryFace_iff_schurFaces_of_polyCP P h00 hpoly).mpr hbound
  have hg : T < Rho5.GrowthModel.growthRatio P
      [1, p P, k P, r P, |Rho5.CanonicalTail.delta P|] := by
    rw [← hfacts.trace_eq, hfacts.growth_eq_rho]
    exact hlt
  exact ⟨P, h00, hpoly, hminor.1, hminor.2, hface,
    (Rho5.MinorGrowthThreshold.threshold_lt_iff hfacts.entryMax h00 hfacts.cp0 hfacts.cp4
      hfacts.cp3 hfacts.p_pos hfacts.k_pos hfacts.r_pos hT).mp hg⟩

/-- **The sorted-boundary global equivalence.**  For every `T ≥ 4`, the global growth
bound is *exactly* the pair of polynomial inequalities on the actual sorted four-boundary
domain. -/
theorem rho5Trace_le_iff_sorted_boundary {T : ℝ} (hT : 4 ≤ T) :
    Rho5.GrowthSupremum.rho5Trace ≤ T ↔
      ∀ M : Matrix5, M 0 0 = 1 → Rho5.MinorCPDomain.PolyCP M →
        0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
          Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
            Rho5.MinorBoundaryFaces.BoundaryFace M →
              (Rho5.MinorGrowthThreshold.C M ≤ T * Rho5.MinorGrowthThreshold.B M ∧
                |M.det| ≤ T * Rho5.MinorGrowthThreshold.C M) := by
  constructor
  · exact inequalities_of_rho5Trace_le_sorted hT
  · intro h
    by_contra hnot
    have hlt : T < Rho5.GrowthSupremum.rho5Trace := lt_of_not_ge hnot
    obtain ⟨M, h00, hpoly, hm1, hm2, hface, hviol⟩ :=
      exists_counterexample_of_lt_rho5Trace hT hlt
    rcases hviol with h1 | h1
    · exact absurd (h M h00 hpoly hm1 hm2 hface).1 (not_le.mpr h1)
    · exact absurd (h M h00 hpoly hm1 hm2 hface).2 (not_le.mpr h1)

/-- **Strict-violation form.**  `T` is strictly below the global bound exactly when some
actual sorted boundary matrix violates one of the two inequalities strictly. -/
theorem rho5Trace_lt_iff_exists {T : ℝ} (hT : 4 ≤ T) :
    T < Rho5.GrowthSupremum.rho5Trace ↔
      ∃ M : Matrix5, M 0 0 = 1 ∧ Rho5.MinorCPDomain.PolyCP M ∧
        0 ≤ Rho5.MinorCPDomain.m4 M 0 1 ∧
          Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 ∧
            Rho5.MinorBoundaryFaces.BoundaryFace M ∧
              (T * Rho5.MinorGrowthThreshold.B M < Rho5.MinorGrowthThreshold.C M ∨
                T * Rho5.MinorGrowthThreshold.C M < |M.det|) := by
  constructor
  · exact exists_counterexample_of_lt_rho5Trace hT
  · rintro ⟨M, h00, hpoly, hm1, hm2, hface, hviol⟩
    by_contra hnot
    have hle : Rho5.GrowthSupremum.rho5Trace ≤ T := le_of_not_gt hnot
    have hc := Rho5.GlobalMinorReduction.inequalities_of_rho5Trace_le hT hle M h00 hpoly
    rcases hviol with h1 | h1
    · exact absurd hc.1 (not_le.mpr h1)
    · exact absurd hc.2 (not_le.mpr h1)

/-- **The four-obligation certificate corollary.**  One upper-bound proof per face — each
under the common feasible/sorted premises and `T ≥ 4` — is enough for the global bound.
The four faces are supplied in D70's Schur form and converted internally to D70's own
`BoundaryFace`; this corollary proves none of the four inequalities itself. -/
theorem rho5Trace_le_of_four_face_bounds {T : ℝ} (hT : 4 ≤ T)
    (hf1 : ∀ M : Matrix5, M 0 0 = 1 → Rho5.MinorCPDomain.PolyCP M →
      0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
        Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
          M 4 4 = -1 →
            (Rho5.MinorGrowthThreshold.C M ≤ T * Rho5.MinorGrowthThreshold.B M ∧
              |M.det| ≤ T * Rho5.MinorGrowthThreshold.C M))
    (hf2 : ∀ M : Matrix5, M 0 0 = 1 → Rho5.MinorCPDomain.PolyCP M →
      0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
        Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
          S4 M 3 3 = -p M →
            (Rho5.MinorGrowthThreshold.C M ≤ T * Rho5.MinorGrowthThreshold.B M ∧
              |M.det| ≤ T * Rho5.MinorGrowthThreshold.C M))
    (hf3 : ∀ M : Matrix5, M 0 0 = 1 → Rho5.MinorCPDomain.PolyCP M →
      0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
        Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
          S3 M 2 2 = -k M →
            (Rho5.MinorGrowthThreshold.C M ≤ T * Rho5.MinorGrowthThreshold.B M ∧
              |M.det| ≤ T * Rho5.MinorGrowthThreshold.C M))
    (hf4 : ∀ M : Matrix5, M 0 0 = 1 → Rho5.MinorCPDomain.PolyCP M →
      0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
        Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
          T2 M 1 1 = -r M →
            (Rho5.MinorGrowthThreshold.C M ≤ T * Rho5.MinorGrowthThreshold.B M ∧
              |M.det| ≤ T * Rho5.MinorGrowthThreshold.C M)) :
    Rho5.GrowthSupremum.rho5Trace ≤ T := by
  refine (rho5Trace_le_iff_sorted_boundary hT).mpr ?_
  intro M h00 hpoly hm1 hm2 hface
  rcases (Rho5.MinorBoundaryFaces.boundaryFace_iff_schurFaces_of_polyCP M h00 hpoly).mp
    hface with h | h | h | h
  · exact hf1 M h00 hpoly hm1 hm2 h
  · exact hf2 M h00 hpoly hm1 hm2 h
  · exact hf3 M h00 hpoly hm1 hm2 h
  · exact hf4 M h00 hpoly hm1 hm2 h

end Rho5.BoundaryUpperReduction
