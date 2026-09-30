import Rho5.Shared.MainlineTreeCover.Box
import Mathlib.Data.List.Basic

/-!
# Finite binary coverage with explicit leaf obligations

This module records every leaf, including any leaf that an external campaign
calls OPEN.  Coverage alone does not prove exclusion or a height bound.
`safe_of_all_leaves` requires the desired conclusion on every enumerated leaf;
`safe_or_open_leaf` retains the unresolved leaf in its conclusion.

The tree carries rational split points and finite coordinate indices.  It has
no matrix assumptions, no certificate checker and no trusted leaf verdict.
Both children contain the split hyperplane.  Coverage needs no interior-split
assumption; `wellFormed` separately makes all leaves subsets of the root.

Source authored for the frozen MainlineTreeCover.Box interface.  Compilation
and integration are performed by the owning mainline, not by this source task.
-/

namespace Rho5.Shared.MainlineTreeCover

/-- A finite split tree.  A leaf is an obligation, not a proof of safety. -/
inductive Tree (n : ℕ) where
  | leaf : Tree n
  | split (j : Fin n) (c : ℚ) (leftTree rightTree : Tree n) : Tree n

/-- All leaf boxes in left-to-right order.  Equal boxes remain separate entries. -/
def leafBoxes {n : ℕ} (b : Box n) : Tree n → List (Box n)
  | .leaf => [b]
  | .split j c l r =>
      leafBoxes (b.left j c) l ++ leafBoxes (b.right j c) r

/-- Leaf addresses in the same order as `leafBoxes`: false = left, true = right. -/
def leafPaths {n : ℕ} : Tree n → List (List Bool)
  | .leaf => [[]]
  | .split _ _ l r =>
      (leafPaths l).map (fun p => false :: p) ++
      (leafPaths r).map (fun p => true :: p)

/-- Number of internal binary split nodes. -/
def nSplits {n : ℕ} : Tree n → ℕ
  | .leaf => 0
  | .split _ _ l r => 1 + nSplits l + nSplits r

/-- Every declared split lies strictly inside its actual inherited parent box. -/
def wellFormed {n : ℕ} (b : Box n) : Tree n → Prop
  | .leaf => True
  | .split j c l r =>
      b.lo j < c ∧ c < b.hi j ∧
      wellFormed (b.left j c) l ∧ wellFormed (b.right j c) r

/-- The full leaf list covers the root, including shared split boundaries. -/
theorem cover_all_leaves {n : ℕ} (b : Box n) (t : Tree n) :
    ∀ x ∈ b.denote, ∃ a ∈ leafBoxes b t, x ∈ a.denote := by
  induction t generalizing b with
  | leaf =>
      intro x hx
      exact ⟨b, by simp [leafBoxes], hx⟩
  | split j c l r ihl ihr =>
      intro x hx
      rcases Box.split_cover b j c x hx with hl | hr
      · obtain ⟨a, ha, hxa⟩ := ihl (b.left j c) x hl
        refine ⟨a, ?_, hxa⟩
        change a ∈ leafBoxes (b.left j c) l ++ leafBoxes (b.right j c) r
        exact List.mem_append.mpr (Or.inl ha)
      · obtain ⟨a, ha, hxa⟩ := ihr (b.right j c) x hr
        refine ⟨a, ?_, hxa⟩
        change a ∈ leafBoxes (b.left j c) l ++ leafBoxes (b.right j c) r
        exact List.mem_append.mpr (Or.inr ha)

/-- A well-formed tree has no leaf outside its inherited root box. -/
theorem all_leaves_subset {n : ℕ} (b : Box n) (t : Tree n) :
    wellFormed b t → ∀ a ∈ leafBoxes b t, a.denote ⊆ b.denote := by
  induction t generalizing b with
  | leaf =>
      intro _ a ha
      have hab : a = b := by simpa only [leafBoxes, List.mem_singleton] using ha
      subst a
      exact Set.Subset.rfl
  | split j c l r ihl ihr =>
      intro hvalid a ha x hx
      rcases hvalid with ⟨hlo, hhi, hleft, hright⟩
      have hmem : a ∈ leafBoxes (b.left j c) l ∨
          a ∈ leafBoxes (b.right j c) r := by
        simpa only [leafBoxes, List.mem_append] using ha
      rcases hmem with hal | har
      · exact Box.left_subset b j c (le_of_lt hhi)
          (ihl (b.left j c) hleft a hal hx)
      · exact Box.right_subset b j c (le_of_lt hlo)
          (ihr (b.right j c) hright a har hx)

/-- Exact root membership as membership in some complete-list leaf. -/
theorem mem_root_iff_mem_leaf {n : ℕ} (b : Box n) (t : Tree n)
    (hvalid : wellFormed b t) (x : Fin n → ℝ) :
    x ∈ b.denote ↔ ∃ a ∈ leafBoxes b t, x ∈ a.denote := by
  constructor
  · exact cover_all_leaves b t x
  · rintro ⟨a, ha, hx⟩
    exact all_leaves_subset b t hvalid a ha hx

/-- Any pointwise conclusion valid on every leaf pulls back to the root. -/
theorem safe_of_all_leaves {n : ℕ} (b : Box n) (t : Tree n)
    (P : (Fin n → ℝ) → Prop)
    (hleaves : ∀ a ∈ leafBoxes b t, ∀ x ∈ a.denote, P x) :
    ∀ x ∈ b.denote, P x := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := cover_all_leaves b t x hx
  exact hleaves a ha x hxa

/-- The two-child form of pointwise safety pullback. -/
theorem safe_of_children {n : ℕ} (b : Box n) (j : Fin n) (c : ℚ)
    (P : (Fin n → ℝ) → Prop)
    (hl : ∀ x ∈ (b.left j c).denote, P x)
    (hr : ∀ x ∈ (b.right j c).denote, P x) :
    ∀ x ∈ b.denote, P x := by
  intro x hx
  rcases Box.split_cover b j c x hx with hxl | hxr
  · exact hl x hxl
  · exact hr x hxr

/-- A partial proof leaves an explicit open-leaf alternative.
The predicate `closed` is not trusted: its safety implication is a hypothesis. -/
theorem safe_or_open_leaf {n : ℕ} (b : Box n) (t : Tree n)
    (P : (Fin n → ℝ) → Prop) (closed : Box n → Prop)
    (hclosed : ∀ a ∈ leafBoxes b t, closed a → ∀ x ∈ a.denote, P x) :
    ∀ x ∈ b.denote,
      P x ∨ ∃ a ∈ leafBoxes b t, ¬ closed a ∧ x ∈ a.denote := by
  classical
  intro x hx
  obtain ⟨a, ha, hxa⟩ := cover_all_leaves b t x hx
  by_cases hc : closed a
  · exact Or.inl (hclosed a ha hc x hxa)
  · exact Or.inr ⟨a, ha, hc, hxa⟩

/-- Every finite full binary tree has one more leaf than split nodes. -/
theorem length_leafBoxes {n : ℕ} (b : Box n) (t : Tree n) :
    (leafBoxes b t).length = nSplits t + 1 := by
  induction t generalizing b with
  | leaf => simp [leafBoxes, nSplits]
  | split j c l r ihl ihr =>
      simp [leafBoxes, nSplits, ihl, ihr,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The address traversal contains every leaf occurrence. -/
theorem length_leafPaths {n : ℕ} (t : Tree n) :
    (leafPaths t).length = nSplits t + 1 := by
  induction t with
  | leaf => simp [leafPaths, nSplits]
  | split j c l r ihl ihr =>
      simp [leafPaths, nSplits, ihl, ihr,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Addresses and boxes have matching traversal lengths. -/
theorem length_leafPaths_eq_leafBoxes {n : ℕ} (b : Box n) (t : Tree n) :
    (leafPaths t).length = (leafBoxes b t).length := by
  rw [length_leafPaths, length_leafBoxes]

end Rho5.Shared.MainlineTreeCover
