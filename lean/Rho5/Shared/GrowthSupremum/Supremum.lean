/-
D18 — the growth supremum `rho5Trace` and its coarse bounds
===========================================================

**Item 2 (definition and bounds).** `rho5Trace` is the supremum of the *actual* growth
values of legal traces:

  `noncomputable def rho5Trace : ℝ := sSup Rho5.GrowthModel.GrowthValues`

Both side conditions are paid before the supremum is used, as the card requires:
nonemptiness (`growthValues_nonempty`, item 1) and boundedness
(`bddAbove_growthValues`).  On top of them:

* `1 ≤ rho5Trace ≤ 16` (`one_le_rho5Trace_le_sixteen`);
* `rho5Trace` is an upper bound of every growth value (`le_rho5Trace`);
* the universal property `rho5Trace ≤ B ↔ ∀ g ∈ GrowthValues, g ≤ B`
  (`rho5Trace_le_iff`).

Scope note (frozen by the card): this is the supremum of a genuinely path-defined set
with a *coarse* bound.  It is **not** claimed that `rho5Trace` equals the alpha of the
manuscript, that the supremum is attained, or that the original main theorems are
closed; no such statement appears anywhere in this module.
-/
import Rho5.Shared.GrowthSupremum.Bounds
import Mathlib.Data.Real.Archimedean

namespace Rho5.GrowthSupremum

open Rho5

/-- **Item 2 (definition).** The RHO5 growth supremum: the supremum of the growth
values of all legal elimination traces of nonzero `5 × 5` matrices.

This is a definition over the real numbers, evaluated with the frozen
`Rho5.GrowthModel.GrowthValues`; it is not claimed to be attained and is not
identified with any external constant. -/
noncomputable def rho5Trace : ℝ := sSup Rho5.GrowthModel.GrowthValues

/-- Defining equation, kept for rewriting. -/
theorem rho5Trace_eq : rho5Trace = sSup Rho5.GrowthModel.GrowthValues := rfl

/-- **Item 2 (upper bound property).** Every growth value is at most `rho5Trace`. -/
theorem le_rho5Trace {g : ℝ} (hg : g ∈ Rho5.GrowthModel.GrowthValues) : g ≤ rho5Trace := by
  rw [rho5Trace_eq]
  exact le_csSup bddAbove_growthValues hg

/-- **Item 2 (lower bound).** `1 ≤ rho5Trace`: some growth value exists (item 1) and all
of them are at least `1`. -/
theorem one_le_rho5Trace : 1 ≤ rho5Trace := by
  obtain ⟨g, hg⟩ := growthValues_nonempty
  exact le_trans (one_le_of_mem_growthValues hg) (le_rho5Trace hg)

/-- **Item 2 (upper bound).** `rho5Trace ≤ 16`, the coarse bound: the supremum of a set
all of whose members are `≤ 16` is `≤ 16`. -/
theorem rho5Trace_le_sixteen : rho5Trace ≤ 16 := by
  rw [rho5Trace_eq]
  exact csSup_le growthValues_nonempty (fun _ hg => le_sixteen_of_mem_growthValues hg)

/-- **Item 2 (both bounds together).** `1 ≤ rho5Trace ≤ 16`. -/
theorem one_le_rho5Trace_le_sixteen : 1 ≤ rho5Trace ∧ rho5Trace ≤ 16 :=
  ⟨one_le_rho5Trace, rho5Trace_le_sixteen⟩

/-- Nonemptiness, in the form the supremum API consumes. -/
theorem rho5Trace_nonempty_paid : (Rho5.GrowthModel.GrowthValues).Nonempty :=
  growthValues_nonempty

/-- Boundedness, in the form the supremum API consumes. -/
theorem rho5Trace_bddAbove_paid : BddAbove Rho5.GrowthModel.GrowthValues :=
  bddAbove_growthValues

/-- **Item 2 (universal property).** For every real `B`, `rho5Trace ≤ B` exactly when
every legal growth value is at most `B`.  This is the interface later certificates
consume; it uses the paid nonemptiness and boundedness. -/
theorem rho5Trace_le_iff (B : ℝ) :
    rho5Trace ≤ B ↔ ∀ g ∈ Rho5.GrowthModel.GrowthValues, g ≤ B := by
  rw [rho5Trace_eq]
  exact csSup_le_iff bddAbove_growthValues growthValues_nonempty

/-- `rho5Trace` is the least upper bound of the growth values, in the `IsLUB` form. -/
theorem isLUB_rho5Trace : IsLUB Rho5.GrowthModel.GrowthValues rho5Trace := by
  rw [rho5Trace_eq]
  exact isLUB_csSup growthValues_nonempty bddAbove_growthValues

end Rho5.GrowthSupremum
