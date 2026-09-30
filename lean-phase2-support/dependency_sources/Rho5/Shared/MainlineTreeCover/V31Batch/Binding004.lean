import Rho5.Shared.MainlineTreeCover.V31Batch.Rows004
import Rho5.Shared.MainlineTreeCover.V31Batch.GeometryBindings
import Rho5.Shared.MainlineTreeCover.V31Batch.GenericSourceBridge

/-! Actual original source to the concrete terminal at path 000000111.
All support-row and current-box equalities are proved in imported instance
modules. Only the original polynomial feasibility is assumed; no LP row,
leaf emptiness, matrix/global chart coverage, or parser oracle is assumed. -/
namespace Rho5.Shared.MainlineTreeCover.V31Batch.Binding004

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem lower (j : Fin 57) :
    Leaf004.rationalSystem.lo j = (Model.liftedBox GeometryBindings.flatBox4).lo j := by
  rw [GeometryBindings.lifted_flatBox4_lo]
  change (([8816, 9918, -9600, -9600, -9600, 636, 318, 4959, 159, 159, 0, 0, 0, -4800, -4800, -4800, -4800, -4800, 0, -9600, -9600, -9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -23040000, -23040000, 0, -23040000, -23040000, 0, -23040000, -23040000, 0, -23040000, -23040000, 0, 0, 0, 25281, -46080000, -46080000, -46080000, -43027200, -46080000, -43027200, -46080000, 43718544, 2803488, 5606976] : List ℤ).getD j.val 0 : ℚ) /
    (if j.val < 22 then 4800 else 23040000) = GeometryBindings.normalizedLo4 j
  fin_cases j <;> norm_num [GeometryBindings.normalizedLo4]

theorem upper (j : Fin 57) :
    Leaf004.rationalSystem.hi j = (Model.liftedBox GeometryBindings.flatBox4).hi j := by
  rw [GeometryBindings.lifted_flatBox4_hi]
  change (([9600, 18882, -318, -636, -636, 4800, 4482, 9600, 4800, 4800, 4800, 4800, 4800, 0, 0, 0, 4800, 4800, 4800, 0, 0, 0, 46080000, 46080000, 46080000, 46080000, 46080000, 46080000, 46080000, 46080000, 46080000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 0, 0, 0, -202248, -404496, -202248, -404496, 92160000, 43027200, 46080000] : List ℤ).getD j.val 0 : ℚ) /
    (if j.val < 22 then 4800 else 23040000) = GeometryBindings.normalizedHi4 j
  fin_cases j <;> norm_num [GeometryBindings.normalizedHi4]

/-- The original C format requires strictly positive support weights. -/
theorem weights_positive : ∀ i : Fin 33, 0 < Leaf004.data.weights.getD i.val 0 := by decide

theorem support_ids_count : Leaf004.supportIds.length = 33 := by rfl

/-- Same original point and its actual shared products; current leaf rows. -/
theorem source_feasible (x : Fin 22 → ℝ) (hx : Model.SameSource x)
    (hb : x ∈ FiveTree.leaf4.denote) :
    Rho5.Shared.CertificateRules.Rational.FeasibleR Leaf004.rationalSystem (Model.liftedPoint x) := by
  have hb' : x ∈ GeometryBindings.flatBox4.denote := by
    rwa [GeometryBindings.flatBox4_eq_leaf4]
  obtain ⟨hbox, hrows⟩ := Model.model_source_on_box GeometryBindings.flatBox4 x hb' hx
  exact ratFeasibleR_of_source_rows _ _ _ Rows004.selectedId lower upper Rows004.all_rows Rows004.all_rhs _ hbox hrows

theorem source_impossible (x : Fin 22 → ℝ) (hx : Model.SameSource x)
    (hb : x ∈ FiveTree.leaf4.denote) : False :=
  Leaf004.rational_empty_real _ (source_feasible x hx hb)

theorem source_leaf_empty : Model.source ∩ FiveTree.leaf4.denote ⊆ ∅ := by
  intro x hx
  exact False.elim (source_impossible x hx.1 hx.2)

end Rho5.Shared.MainlineTreeCover.V31Batch.Binding004
