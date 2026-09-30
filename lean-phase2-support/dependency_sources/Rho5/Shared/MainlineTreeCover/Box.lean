import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
M01: closed rational boxes interpreted over REAL points.
Both split children include the cut plane. No leaf is declared infeasible here.
An empty or degenerate box is permitted; strict interior cuts are a separate
certificate-format qualification, not an implicit nonempty-box assumption.
-/
namespace Rho5.Shared.MainlineTreeCover

structure Box (n : ℕ) where
  lo : Fin n → ℚ
  hi : Fin n → ℚ

namespace Box

def denote {n : ℕ} (b : Box n) : Set (Fin n → ℝ) :=
  {x | ∀ i, (b.lo i : ℝ) ≤ x i ∧ x i ≤ (b.hi i : ℝ)}

def left {n : ℕ} (b : Box n) (j : Fin n) (c : ℚ) : Box n :=
  ⟨b.lo, Function.update b.hi j c⟩

def right {n : ℕ} (b : Box n) (j : Fin n) (c : ℚ) : Box n :=
  ⟨Function.update b.lo j c, b.hi⟩

/-- Valid V31 splits are strict, although the child boxes themselves are closed. -/
def ValidCut {n : ℕ} (b : Box n) (j : Fin n) (c : ℚ) : Prop :=
  b.lo j < c ∧ c < b.hi j

theorem mem_left_of_le {n : ℕ} (b : Box n) (j : Fin n) (c : ℚ)
    {x : Fin n → ℝ} (hx : x ∈ b.denote) (hc : x j ≤ (c : ℝ)) :
    x ∈ (b.left j c).denote := by
  intro i
  by_cases hij : i = j
  · subst i
    simpa [left] using And.intro (hx j).1 hc
  · simpa [left, Function.update_of_ne hij] using hx i

theorem mem_right_of_le {n : ℕ} (b : Box n) (j : Fin n) (c : ℚ)
    {x : Fin n → ℝ} (hx : x ∈ b.denote) (hc : (c : ℝ) ≤ x j) :
    x ∈ (b.right j c).denote := by
  intro i
  by_cases hij : i = j
  · subst i
    simpa [right] using And.intro hc (hx j).2
  · simpa [right, Function.update_of_ne hij] using hx i

theorem split_cover {n : ℕ} (b : Box n) (j : Fin n) (c : ℚ) :
    ∀ x ∈ b.denote,
      x ∈ (b.left j c).denote ∨ x ∈ (b.right j c).denote := by
  intro x hx
  rcases le_total (x j) (c : ℝ) with h | h
  · exact Or.inl (mem_left_of_le b j c hx h)
  · exact Or.inr (mem_right_of_le b j c hx h)

theorem left_subset {n : ℕ} (b : Box n) (j : Fin n) (c : ℚ)
    (hc : c ≤ b.hi j) : (b.left j c).denote ⊆ b.denote := by
  intro x hx i
  by_cases hij : i = j
  · subst i
    have h : (b.lo j : ℝ) ≤ x j ∧ x j ≤ (c : ℝ) := by
      simpa [left] using hx j
    exact ⟨h.1, h.2.trans (by exact_mod_cast hc)⟩
  · simpa [left, Function.update_of_ne hij] using hx i

theorem right_subset {n : ℕ} (b : Box n) (j : Fin n) (c : ℚ)
    (hc : b.lo j ≤ c) : (b.right j c).denote ⊆ b.denote := by
  intro x hx i
  by_cases hij : i = j
  · subst i
    have h : (c : ℝ) ≤ x j ∧ x j ≤ (b.hi j : ℝ) := by
      simpa [right] using hx j
    exact ⟨(by exact_mod_cast hc : (b.lo j : ℝ) ≤ (c : ℝ)).trans h.1, h.2⟩
  · simpa [right, Function.update_of_ne hij] using hx i

theorem split_union {n : ℕ} (b : Box n) (j : Fin n) (c : ℚ)
    (hc : b.lo j ≤ c ∧ c ≤ b.hi j) :
    (b.left j c).denote ∪ (b.right j c).denote = b.denote := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with h | h
    · exact left_subset b j c hc.2 h
    · exact right_subset b j c hc.1 h
  · intro x hx
    exact split_cover b j c x hx

theorem cut_plane_in_both {n : ℕ} (b : Box n) (j : Fin n) (c : ℚ)
    {x : Fin n → ℝ} (hx : x ∈ b.denote) (hc : x j = (c : ℝ)) :
    x ∈ (b.left j c).denote ∩ (b.right j c).denote :=
  ⟨mem_left_of_le b j c hx hc.le, mem_right_of_le b j c hx hc.ge⟩

def midpoint {n : ℕ} (b : Box n) (j : Fin n) : ℚ :=
  (b.lo j + b.hi j) / 2

theorem midpoint_valid {n : ℕ} (b : Box n) (j : Fin n)
    (h : b.lo j < b.hi j) : b.ValidCut j (b.midpoint j) := by
  dsimp [ValidCut, midpoint]
  constructor <;> linarith

theorem midpoint_union {n : ℕ} (b : Box n) (j : Fin n)
    (h : b.lo j < b.hi j) :
    (b.left j (b.midpoint j)).denote ∪ (b.right j (b.midpoint j)).denote =
      b.denote :=
  split_union b j (b.midpoint j)
    ⟨(midpoint_valid b j h).1.le, (midpoint_valid b j h).2.le⟩

theorem ext {n : ℕ} (a b : Box n)
    (hl : ∀ i, a.lo i = b.lo i) (hh : ∀ i, a.hi i = b.hi i) : a = b := by
  cases a
  cases b
  congr
  · exact funext hl
  · exact funext hh

/-- A zero-width coordinate admits no strict split. -/
theorem no_valid_cut_of_zero_width {n : ℕ} (b : Box n) (j : Fin n)
    (h : b.lo j = b.hi j) : ∀ c, ¬ b.ValidCut j c := by
  intro c hc
  rcases hc with ⟨h1, h2⟩
  rw [h] at h1
  exact (lt_irrefl _) (h1.trans h2)

end Box
end Rho5.Shared.MainlineTreeCover
