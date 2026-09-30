import Rho5.Shared.MainlineTreeCover.V31Prefix

/-!
# M02: geometry of the five-leaf sibling rooted at `0000001`

The source section is records 8--16 (zero based):
`S 12; S 16; C; C; S 18; S 17; C; C; C`.
These nine raw lines were read directly from the frozen archive member
`rho5_v31_exact/small_exact.tree.gz`; their uncompressed-byte SHA256 is
`2a1e40d31a397b436f2321a9f4a0dec9401b18923e1f22b60cc0c97fbe42bddd`.
All four actual inherited midpoint cuts are zero. Indices are in the original
22-coordinate order, not the lifted order. The root is the already bound M01
literal `V31Prefix.actualLeafBox1`.

This file proves closed-box geometry and source-restricted coverage only.
Every C remains an unpaid leaf obligation. Raw archive parsing, record-number
transcription and provenance hashes are external data-binding responsibilities;
they are not asserted to be checked by these geometric Lean theorems.

Authored source: compilation and axiom checks are pending owner integration.
-/

namespace Rho5.Shared.MainlineTreeCover.V31Batch.FiveTree

def subRoot : Box 22 := V31Prefix.actualLeafBox1

def left12 : Box 22 := subRoot.left (12 : Fin 22) (0 : ℚ)

def right12 : Box 22 := subRoot.right (12 : Fin 22) (0 : ℚ)

def right12Left18 : Box 22 := right12.left (18 : Fin 22) (0 : ℚ)

/-- Source record 10, relative address `00`. -/
def leaf0 : Box 22 := left12.left (16 : Fin 22) (0 : ℚ)

/-- Source record 11, relative address `01`. -/
def leaf1 : Box 22 := left12.right (16 : Fin 22) (0 : ℚ)

/-- Source record 14, relative address `100`. -/
def leaf2 : Box 22 := right12Left18.left (17 : Fin 22) (0 : ℚ)

/-- Source record 15, relative address `101`. -/
def leaf3 : Box 22 := right12Left18.right (17 : Fin 22) (0 : ℚ)

/-- Source record 16, relative address `11`. -/
def leaf4 : Box 22 := right12.right (18 : Fin 22) (0 : ℚ)

def tree : Tree 22 :=
  .split (12 : Fin 22) (0 : ℚ)
    (.split (16 : Fin 22) (0 : ℚ) .leaf .leaf)
    (.split (18 : Fin 22) (0 : ℚ)
      (.split (17 : Fin 22) (0 : ℚ) .leaf .leaf) .leaf)

def fiveLeaves : List (Box 22) := [leaf0, leaf1, leaf2, leaf3, leaf4]

def splitAxes : List (Fin 22) := [12, 16, 18, 17]

theorem splitAxes_values : splitAxes.map Fin.val = [12, 16, 18, 17] := by
  rfl

theorem cut12_midpoint : subRoot.midpoint (12 : Fin 22) = (0 : ℚ) := by
  change ((-4800 : ℚ) / 4800 + (4800 : ℚ) / 4800) / 2 = 0
  norm_num

theorem cut12_valid : subRoot.ValidCut (12 : Fin 22) (0 : ℚ) := by
  change (-4800 : ℚ) / 4800 < 0 ∧ (0 : ℚ) < (4800 : ℚ) / 4800
  norm_num

theorem cut16_midpoint : left12.midpoint (16 : Fin 22) = (0 : ℚ) := by
  change ((-4800 : ℚ) / 4800 + (4800 : ℚ) / 4800) / 2 = 0
  norm_num

theorem cut16_valid : left12.ValidCut (16 : Fin 22) (0 : ℚ) := by
  change (-4800 : ℚ) / 4800 < 0 ∧ (0 : ℚ) < (4800 : ℚ) / 4800
  norm_num

theorem cut18_midpoint : right12.midpoint (18 : Fin 22) = (0 : ℚ) := by
  change ((-4800 : ℚ) / 4800 + (4800 : ℚ) / 4800) / 2 = 0
  norm_num

theorem cut18_valid : right12.ValidCut (18 : Fin 22) (0 : ℚ) := by
  change (-4800 : ℚ) / 4800 < 0 ∧ (0 : ℚ) < (4800 : ℚ) / 4800
  norm_num

theorem cut17_midpoint : right12Left18.midpoint (17 : Fin 22) = (0 : ℚ) := by
  change ((-4800 : ℚ) / 4800 + (4800 : ℚ) / 4800) / 2 = 0
  norm_num

theorem cut17_valid : right12Left18.ValidCut (17 : Fin 22) (0 : ℚ) := by
  change (-4800 : ℚ) / 4800 < 0 ∧ (0 : ℚ) < (4800 : ℚ) / 4800
  norm_num

theorem tree_wellFormed : wellFormed subRoot tree := by
  exact ⟨cut12_valid.1, cut12_valid.2,
    ⟨cut16_valid.1, cut16_valid.2, True.intro, True.intro⟩,
    ⟨cut18_valid.1, cut18_valid.2,
      ⟨cut17_valid.1, cut17_valid.2, True.intro, True.intro⟩,
      True.intro⟩⟩

theorem four_splits : nSplits tree = 4 := by
  rfl

theorem leafBoxes_tree : leafBoxes subRoot tree = fiveLeaves := by
  rfl

theorem five_leaves : (leafBoxes subRoot tree).length = 5 := by
  rfl

theorem leafPaths_tree : leafPaths tree =
    [[false, false], [false, true], [true, false, false],
      [true, false, true], [true, true]] := by
  rfl

def rootPath : List Bool := [false, false, false, false, false, false, true]

def fullPaths : List (List Bool) := (leafPaths tree).map (rootPath ++ ·)

/-- Full original-tree addresses, in the same order as `fiveLeaves`. -/
theorem fullPaths_values : fullPaths =
    [[false, false, false, false, false, false, true, false, false],
     [false, false, false, false, false, false, true, false, true],
     [false, false, false, false, false, false, true, true, false, false],
     [false, false, false, false, false, false, true, true, false, true],
     [false, false, false, false, false, false, true, true, true]] := by
  rfl

theorem fullPaths_length : fullPaths.length = 5 := by
  rfl

/-- Every point of the complete subtree root belongs to some displayed leaf. -/
theorem subtree_cover :
    ∀ x ∈ subRoot.denote, ∃ b ∈ fiveLeaves, x ∈ b.denote := by
  simpa only [leafBoxes_tree] using cover_all_leaves subRoot tree

/-- Actual inherited cuts also prove that no displayed leaf leaves its root. -/
theorem leaves_subset_root :
    ∀ b ∈ fiveLeaves, b.denote ⊆ subRoot.denote := by
  simpa only [leafBoxes_tree] using
    all_leaves_subset subRoot tree tree_wellFormed

theorem mem_subRoot_iff (x : Fin 22 → ℝ) :
    x ∈ subRoot.denote ↔ ∃ b ∈ fiveLeaves, x ∈ b.denote := by
  simpa only [leafBoxes_tree] using
    mem_root_iff_mem_leaf subRoot tree tree_wellFormed x

/-- The same source is retained at all five leaves, including cut boundaries. -/
theorem source_cover (source : Set (Fin 22 → ℝ)) :
    ∀ x ∈ source ∩ subRoot.denote,
      ∃ b ∈ fiveLeaves, x ∈ source ∩ b.denote := by
  intro x hx
  obtain ⟨b, hb, hxb⟩ := subtree_cover x hx.2
  exact ⟨b, hb, hx.1, hxb⟩

/-- Conditional pullback only: every leaf's same-source obligation is explicit. -/
theorem source_safe_of_five (source : Set (Fin 22 → ℝ))
    (P : (Fin 22 → ℝ) → Prop)
    (h : ∀ b ∈ fiveLeaves, ∀ x ∈ source ∩ b.denote, P x) :
    ∀ x ∈ source ∩ subRoot.denote, P x := by
  intro x hx
  obtain ⟨b, hb, hxb⟩ := source_cover source x hx
  exact h b hb x hxb

/-- No C is proved here: this consumes five independently supplied exclusions. -/
theorem source_empty_of_five (source : Set (Fin 22 → ℝ))
    (h : ∀ b ∈ fiveLeaves, source ∩ b.denote ⊆ ∅) :
    source ∩ subRoot.denote ⊆ ∅ := by
  intro x hx
  obtain ⟨b, hb, hxb⟩ := source_cover source x hx
  exact h b hb hxb

/-- M01's other seven boxes, retaining its first C-record box unchanged. -/
def remainingSeven : List (Box 22) :=
  [V31Prefix.actualLeafBox0, V31Prefix.actualLeafBox2,
   V31Prefix.actualLeafBox3, V31Prefix.actualLeafBox4,
   V31Prefix.actualLeafBox5, V31Prefix.actualLeafBox6,
   V31Prefix.actualLeafBox7]

theorem remainingSeven_length : remainingSeven.length = 7 := by
  rfl

/-- Set-membership partition only; no disjointness of closed boxes is claimed. -/
theorem frontier_partition (b : Box 22) :
    b ∈ V31Prefix.actualFrontier ↔ b = subRoot ∨ b ∈ remainingSeven := by
  simp only [V31Prefix.actualFrontier, remainingSeven, subRoot,
    List.mem_cons, List.mem_singleton, or_assoc, or_left_comm, or_comm]

/-- A point of the old root is either in a retained box or in a new leaf. -/
theorem root_refined_cover :
    ∀ x ∈ V31Prefix.root.denote,
      (∃ b ∈ remainingSeven, x ∈ b.denote) ∨
      (∃ b ∈ fiveLeaves, x ∈ b.denote) := by
  intro x hx
  obtain ⟨b, hb, hxb⟩ := V31Prefix.prefix_cover x hx
  rcases (frontier_partition b).mp hb with hsub | hrem
  · subst b
    exact Or.inr (subtree_cover x hxb)
  · exact Or.inl ⟨b, hrem, hxb⟩

/-- Removing this subtree requires emptiness of source INTERSECT subroot.
The first C record and the six larger M01 siblings remain unresolved here. -/
theorem remainingSeven_cover (source : Set (Fin 22 → ℝ))
    (hsource : source ⊆ V31Prefix.root.denote)
    (hnosub : source ∩ subRoot.denote ⊆ ∅) :
    ∀ x ∈ source, ∃ b ∈ remainingSeven, x ∈ source ∩ b.denote := by
  intro x hx
  obtain ⟨b, hb, hxb⟩ := V31Prefix.prefix_cover x (hsource hx)
  rcases (frontier_partition b).mp hb with hsub | hrem
  · subst b
    exact False.elim (hnosub ⟨hx, hxb⟩)
  · exact ⟨b, hrem, hx, hxb⟩

end Rho5.Shared.MainlineTreeCover.V31Batch.FiveTree
