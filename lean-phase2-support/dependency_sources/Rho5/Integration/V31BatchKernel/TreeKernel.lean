import Rho5.Integration.V31BatchKernel.IntegerRows

namespace Rho5.Integration.V31BatchKernel

inductive TreeCode where
  | terminal (support : Support)
  | split (axis : ℕ) (cut : ℤ) (left right : TreeCode)
  | openLeaf
  deriving DecidableEq, Repr

def mergeVerdicts : Verdict → Verdict → Verdict
  | .invalid, _ => .invalid
  | _, .invalid => .invalid
  | .closed, .closed => .closed
  | _, _ => .pending

theorem mergeVerdicts_closed (a b : Verdict) (h : mergeVerdicts a b = .closed) :
    a = .closed ∧ b = .closed := by
  cases a <;> cases b <;> simp_all [mergeVerdicts]

/-- Both children inherit their box. No leaf-supplied box is trusted. -/
def treeCheck {n k r : ℕ} (m : IntModel n k r) : IBox n → TreeCode → Verdict
  | b, .terminal s => if b.ordered then leafCheck m b s else .invalid
  | b, .openLeaf => if b.ordered then .pending else .invalid
  | b, .split axis cut left right =>
    if h : axis < n then
      let j : Fin n := ⟨axis,h⟩
      if b.ordered && decide (b.lo j < cut ∧ cut < b.hi j ∧ 2*cut = b.lo j+b.hi j) then
        mergeVerdicts (treeCheck m (b.left j cut) left) (treeCheck m (b.right j cut) right)
      else .invalid
    else .invalid

theorem treeCheck_sound {n k r : ℕ} (m : IntModel n k r) (tree : TreeCode) :
    ∀ b, treeCheck m b tree = .closed → ∀ v, b.Contains v → m.Source v → False := by
  induction tree with
  | terminal s =>
    intro b hc v hv hs
    unfold treeCheck at hc
    split at hc
    · exact leafCheck_sound m b s hc v hv hs
    · cases hc
  | openLeaf =>
    intro b hc v hv hs
    unfold treeCheck at hc
    split at hc <;> cases hc
  | split axis cut left right ihl ihr =>
    intro b hc v hv hs
    unfold treeCheck at hc
    split at hc
    · rename_i hj
      dsimp only at hc
      split at hc
      · have hh := mergeVerdicts_closed _ _ hc
        rcases b.split_cover ⟨axis,hj⟩ cut v hv with hl | hr
        · exact ihl _ hh.1 v hl hs
        · exact ihr _ hh.2 v hr hs
      · cases hc
    · cases hc

/-- An externally supplied entry must exactly match the fixed positive scale and box. -/
def checkedEntry {n k r : ℕ} (expectedScale : ℤ) (expectedBox : IBox n)
    (suppliedScale : ℤ) (suppliedBox : IBox n) (m : IntModel n k r) (tree : TreeCode) : Verdict :=
  if decide (0 < expectedScale ∧ suppliedScale = expectedScale ∧
      (∀ j, suppliedBox.lo j = expectedBox.lo j ∧ suppliedBox.hi j = expectedBox.hi j)) then
    treeCheck m expectedBox tree
  else .invalid

theorem checkedEntry_sound {n k r : ℕ} (T : ℤ) (b : IBox n) (U : ℤ) (c : IBox n)
    (m : IntModel n k r) (tree : TreeCode) (hc : checkedEntry T b U c m tree = .closed)
    (v : Fin n → ℝ) (hv : b.Contains v) (hs : m.Source v) : False := by
  unfold checkedEntry at hc
  split at hc
  · exact treeCheck_sound m tree b hc v hv hs
  · cases hc

end Rho5.Integration.V31BatchKernel
