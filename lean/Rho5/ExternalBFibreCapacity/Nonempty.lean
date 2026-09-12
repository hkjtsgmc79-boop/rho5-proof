import Rho5.ExternalBFibreCapacity.Maximum
import Rho5.ExternalBFibreCapacity.CapacityCount

namespace Rho5.ExternalBFibreCapacity
noncomputable section

/-- The prefix formula itself is feasible from receiver bounds and a nonempty
beta interval. No original feasible p/e pair is assumed here. -/
theorem canonical_left_feasible {f : Frame} (hf : FrameBounds f)
    (hb : BetaFeasible f (betaBar f)) :
    LeftFeasible f (betaBar f) (prefixP f) (prefixE f) := by
  by_cases hp : 0 < betaBar f
  · let w := rows f hf (betaBar f) hp hb.2.1
    have hh := (rows_iff_left f hf _ hp hb.2.1 _ _).mp (row_endpoint_feasible w)
    simpa [prefixP, prefixE, hp, w] using hh
  · have hz : betaBar f = 0 := le_antisymm (le_of_not_gt hp) hb.1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp [prefixP, prefixE, hp, hz]
    intro i
    simpa [prefixP, prefixE, hp, hz] using hf.x_bound i

/-- Only literal frame/interval tests, not an encoded maximum or existence claim. -/
def FrameChecks (f : Frame) : Prop :=
  FrameBounds f ∧ betaZeroChecks f ∧ betaLower f ≤ betaBar f ∧
  (∀ j, |f.q j| ≤ prefixP f) ∧ FixedChecks f (prefixP f) ∧
  EndpointChecks (tailLimits f (prefixP f))

/-- A full any-frame nonemptiness interface. Positive r is explicit and all five
fixed cells and q bounds occur in the checks. -/
theorem complete_fibre_nonempty_iff (f : Frame) :
    (∃ b p e t, Admissible f b p e t) ↔ FrameChecks f := by
  constructor
  · rintro ⟨b,p,e,t,h⟩
    have hm := (prefix_maximum h).1
    have hb : BetaFeasible f b := ⟨h.2.1.beta_nonneg, h.2.1.beta_le_one, h.2.1.right⟩
    have hβ := (beta_interval_nonempty_iff f).mp ⟨b,hb⟩
    have ht := (full_tail_nonempty_iff f (prefixP f)).mp ⟨t,hm.2.2⟩
    exact ⟨h.1, hβ.1, hβ.2, hm.2.1.q_stage, ht.1, ht.2⟩
  · rintro ⟨hf,hz,hβ,hq,hfix,ht⟩
    have hb : BetaFeasible f (betaBar f) :=
      (beta_feasible_iff _ _).mpr ⟨hz,hβ,le_rfl⟩
    have hl := canonical_left_feasible hf hb
    refine ⟨betaBar f,prefixP f,prefixE f,canonicalTail f,hf,?_,?_⟩
    · exact ⟨hl.1,hl.2.1,hl.2.2.1,hb.1,hb.2.1,hl.2.2.2.1,hl.2.2.2.2,hb.2.2,hq⟩
    · exact (tailBounds_iff _ _ _).mpr ⟨hfix,maxTail_feasible ht⟩

/-- Boundary failures are genuine empty *positive-tail* fibres; they do not
silently redefine division at R=0 as attainment. -/
theorem no_source_of_failed_checks (f : Frame) (h : ¬FrameChecks f) :
    ¬∃ b p e t, Admissible f b p e t :=
  fun he => h ((complete_fibre_nonempty_iff f).mp he)

end
end Rho5.ExternalBFibreCapacity
