import Rho5.Shared.MainlineTreeCover.V31Batch.Binding000
import Rho5.Shared.MainlineTreeCover.V31Batch.Binding001
import Rho5.Shared.MainlineTreeCover.V31Batch.Binding002
import Rho5.Shared.MainlineTreeCover.V31Batch.Binding003
import Rho5.Shared.MainlineTreeCover.V31Batch.Binding004

/-! All five actual terminals of the original subtree `0000001` are connected
to the same original polynomial source, at their own current boxes. No leaf
emptiness or generated-row premise remains in this subtree result. The actual
matrix-to-polynomials bridge and every outside sibling remain separate. -/
namespace Rho5.Shared.MainlineTreeCover.V31Batch.FiveSource

theorem all_five_paid (b : Box 22) (hb : b ∈ FiveTree.fiveLeaves) :
    Model.source ∩ b.denote ⊆ ∅ := by
  simp only [FiveTree.fiveLeaves, List.mem_cons, List.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | hnil
  · exact Binding000.source_leaf_empty
  · exact Binding001.source_leaf_empty
  · exact Binding002.source_leaf_empty
  · exact Binding003.source_leaf_empty
  · exact Binding004.source_leaf_empty
  · cases hnil

/-- Complete model exclusion for the actual original records 8 through 16. -/
theorem subtree_model_empty : Model.source ∩ FiveTree.subRoot.denote ⊆ ∅ :=
  FiveTree.source_empty_of_five Model.source all_five_paid

theorem subtree_impossible (x : Fin 22 → ℝ) (hx : Model.SameSource x)
    (hb : x ∈ FiveTree.subRoot.denote) : False :=
  subtree_model_empty ⟨hx, hb⟩

/-- The other seven original M01 frontiers, including D136's first C, remain.
This consumes ONLY the five new leaves, not any unpaid sibling. -/
theorem actual_root_remaining_cover (x : Fin 22 → ℝ) (hx : Model.SameSource x)
    (hroot : x ∈ V31Prefix.root.denote) :
    ∃ b ∈ FiveTree.remainingSeven, x ∈ Model.source ∩ b.denote := by
  rcases FiveTree.root_refined_cover x hroot with hrem | hfive
  · obtain ⟨b,hb,hxbox⟩ := hrem
    exact ⟨b,hb,hx,hxbox⟩
  · obtain ⟨b,hb,hxbox⟩ := hfive
    exact False.elim (all_five_paid b hb ⟨hx,hxbox⟩)

/-- Direct same-source consumer under an independently paid original-root entry. -/
theorem source_remaining_cover (source : Set (Fin 22 → ℝ))
    (hsource : ∀ x ∈ source, Model.SameSource x)
    (hroot : source ⊆ V31Prefix.root.denote) :
    ∀ x ∈ source, ∃ b ∈ FiveTree.remainingSeven, x ∈ source ∩ b.denote := by
  intro x hx
  obtain ⟨b,hb,hxbox⟩ := actual_root_remaining_cover x (hsource x hx) (hroot hx)
  exact ⟨b,hb,hx,hxbox.2⟩

end Rho5.Shared.MainlineTreeCover.V31Batch.FiveSource
