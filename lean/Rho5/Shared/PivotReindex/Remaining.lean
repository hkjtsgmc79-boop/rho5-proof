/-
D10 / N03b — the remaining indices after a pivot has been moved to `(0, 0)`
============================================================================

After swapping row `0` with row `p`, the rows other than the active one are the
images of `Fin n` under `remainingIndex p`, defined exactly as the card fixes it:

  `remainingIndex p i = (Equiv.swap 0 p) i.succ`.

Delivered here (the "complete correspondence" obligation):

* `remainingIndex_ne` — the map never returns the pivot index `p`;
* `remainingIndex_injective` — it is injective;
* `remainingIndex_surjective` — every `k ≠ p` is hit;
* `remainingIndex_bijective` and the packaged equivalence `remainingEquiv`, which
  state the three facts at once and are the reusable form for the next stages.

The point of this file is bookkeeping safety: a Schur update that enumerates the
remaining rows by `remainingIndex` cannot silently drop or duplicate a row.  No
enumeration of the 5! permutations is used anywhere. -/
import Mathlib.Data.Fin.SuccPred
import Mathlib.Logic.Equiv.Basic

namespace Rho5.PivotReindex

/-! ## Definition -/

/-- **Item 3 (definition).** The `i`-th remaining index after moving the pivot `p`
to `0`: `(Equiv.swap 0 p) i.succ`.  The successor skips `0`, and the swap sends
`0` to `p`, so the image is exactly the complement of `{p}`. -/
def remainingIndex {n : ℕ} (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  (Equiv.swap 0 p) i.succ

/-- Defining equation, kept for rewriting. -/
theorem remainingIndex_apply {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    remainingIndex p i = (Equiv.swap 0 p) i.succ := rfl

/-! ## The three correspondence facts -/

/-- **Item 3 (never the pivot).** `remainingIndex p i` is never `p`.  Proof: apply
the swap to a hypothetical equality; the involution sends `i.succ` to `0`, which
no successor is. -/
theorem remainingIndex_ne {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    remainingIndex p i ≠ p := by
  intro h
  have h' := congrArg (Equiv.swap 0 p) h
  rw [remainingIndex, Equiv.swap_apply_self, Equiv.swap_apply_right] at h'
  exact Fin.succ_ne_zero i h'

/-- **Item 3 (injectivity).** `remainingIndex p` is injective, so no remaining
index is used twice. -/
theorem remainingIndex_injective {n : ℕ} (p : Fin (n + 1)) :
    Function.Injective (remainingIndex p) := by
  intro i j h
  have h' : i.succ = j.succ := (Equiv.swap 0 p).injective h
  exact Fin.succ_inj.mp h'

/-- **Item 3 (surjectivity).** Every `k ≠ p` is of the form `remainingIndex p i`,
so no remaining index is dropped.  This is the coverage half of the
correspondence and uses `Fin.exists_succ_eq_of_ne_zero`. -/
theorem remainingIndex_surjective {n : ℕ} (p : Fin (n + 1)) :
    ∀ k : Fin (n + 1), k ≠ p → ∃ i : Fin n, remainingIndex p i = k := by
  intro k hk
  have hk0 : (Equiv.swap 0 p) k ≠ 0 := by
    intro h0
    have h' : k = p := by
      have h2 := congrArg (Equiv.swap 0 p) h0
      rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
      exact h2
    exact hk h'
  obtain ⟨i, hi⟩ := Fin.exists_succ_eq_of_ne_zero hk0
  exact ⟨i, by rw [remainingIndex, hi, Equiv.swap_apply_self]⟩

/-- **Item 3 (bijectivity).** The remaining-index map is a bijection from `Fin n`
onto the indices different from `p`. -/
theorem remainingIndex_bijective {n : ℕ} (p : Fin (n + 1)) :
    Function.Bijective
      (fun i : Fin n => (⟨remainingIndex p i, remainingIndex_ne p i⟩ : {k : Fin (n + 1) // k ≠ p})) :=
  ⟨fun _ _ h => remainingIndex_injective p (Subtype.ext_iff.mp h),
   fun k => by
    obtain ⟨i, hi⟩ := remainingIndex_surjective p k.1 k.2
    exact ⟨i, Subtype.ext hi⟩⟩

/-- **Item 3 (packaged equivalence).** The correspondence as a reusable
equivalence: `Fin n ≃ {k : Fin (n + 1) // k ≠ p}`.  This is the form in which the
next stage should carry the remaining rows and columns; it deliberately does not
choose a distinguished representative or an ordering beyond `remainingIndex`. -/
noncomputable def remainingEquiv {n : ℕ} (p : Fin (n + 1)) :
    Fin n ≃ {k : Fin (n + 1) // k ≠ p} where
  toFun i := ⟨remainingIndex p i, remainingIndex_ne p i⟩
  invFun k := Classical.choose (remainingIndex_surjective p k.1 k.2)
  left_inv i :=
    remainingIndex_injective p
      (Classical.choose_spec (remainingIndex_surjective p (remainingIndex p i) (remainingIndex_ne p i)))
  right_inv k :=
    Subtype.ext (Classical.choose_spec (remainingIndex_surjective p k.1 k.2))

/-- The equivalence reads on the first component as `remainingIndex`. -/
@[simp] theorem remainingEquiv_apply_val {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    ((remainingEquiv p) i).1 = remainingIndex p i := rfl

/-- The remaining indices are exactly the indices different from `p`, as a set
equality of the image. -/
theorem remainingIndex_range {n : ℕ} (p : Fin (n + 1)) :
    Set.range (fun i : Fin n => (⟨remainingIndex p i, remainingIndex_ne p i⟩ :
      {k : Fin (n + 1) // k ≠ p})) = (Set.univ : Set {k : Fin (n + 1) // k ≠ p}) :=
  Set.range_eq_univ.mpr (remainingIndex_bijective p).2

/-! ## Interaction with the swap itself -/

/-- The swap undoes the remaining-index map: `swap 0 p (remainingIndex p i) = i.succ`. -/
@[simp] theorem swap_remainingIndex {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    Equiv.swap 0 p (remainingIndex p i) = i.succ := by
  rw [remainingIndex, Equiv.swap_apply_self]

/-- **Item 3 (exactly one).** Every `k ≠ p` is hit by *exactly one* remaining
index.  This is the form in which the next stage should read the correspondence:
existence is coverage, uniqueness is injectivity, and no choice of ordering beyond
`remainingIndex` is involved. -/
theorem existsUnique_remainingIndex {n : ℕ} (p : Fin (n + 1)) {k : Fin (n + 1)}
    (hk : k ≠ p) : ∃! i : Fin n, remainingIndex p i = k := by
  obtain ⟨i, hi⟩ := remainingIndex_surjective p k hk
  exact ⟨i, hi, fun i' hi' => remainingIndex_injective p (by rw [hi', hi])⟩

end Rho5.PivotReindex
