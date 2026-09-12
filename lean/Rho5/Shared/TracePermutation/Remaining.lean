/-
D20 — the remaining row/column bijection induced by a permutation
================================================================

**Item 2, first half.** After the pivot row `p` and column `q` are removed, a
permutation `r` of `Fin (n+1)` induces a permutation of the remaining `n` indices: it
sends the `i`-th remaining index of the source to the `i`-th remaining index of the
target.  This is where the *pivot* is used — `r` alone would not respect the
removal.

The construction is explicit (not `Classical.choose`) and rests on D10's
`Rho5.PivotReindex.remainingEquiv`; the defining property is recorded as
`remainingIndex_remainingPerm`, which is what the Schur correspondence consumes.
-/
import Rho5.Shared.TracePermutation.Permute

namespace Rho5.TracePermutation

open Rho5

/-- The permutation `r` maps the complement of `p` bijectively onto the complement of
`r p` (injectivity of `r` is the whole content).  Explicit form, so that the value of
`toFun` is `r ·` definitionally. -/
noncomputable def subtypePerm {n : ℕ} (r : Equiv.Perm (Fin (n + 1))) (p : Fin (n + 1)) :
    {k : Fin (n + 1) // k ≠ p} ≃ {k : Fin (n + 1) // k ≠ r p} where
  toFun k := ⟨r k.1, fun h => k.2 (r.injective h)⟩
  invFun k := ⟨r.symm k.1, fun h => k.2 (by
    have := congrArg r h
    simpa using this)⟩
  left_inv k := by
    ext
    simp
  right_inv k := by
    ext
    simp

/-- **Item 2 (remaining bijection).** The permutation induced by `r` on the `n`
remaining indices when the pivot `p` is moved: source remaining index `i` goes to the
remaining index that `r` sends it to (relative to `r p` in the target). -/
noncomputable def remainingPerm {n : ℕ} (r : Equiv.Perm (Fin (n + 1))) (p : Fin (n + 1)) :
    Equiv.Perm (Fin n) :=
  (Rho5.PivotReindex.remainingEquiv p).trans
    ((subtypePerm r p).trans (Rho5.PivotReindex.remainingEquiv (r p)).symm)

/-- **Item 2 (defining property).** The remaining bijection is exactly the one that
carries D10's remaining indices across: the `i`-th remaining index of the target is
the image under `r` of the `i`-th remaining index of the source.

This is the statement the Schur correspondence is proved from; note that it is a
*cross-index* identity, not an equality of matrices under a fixed `Fin` numbering. -/
theorem remainingIndex_remainingPerm {n : ℕ} (r : Equiv.Perm (Fin (n + 1)))
    (p : Fin (n + 1)) (i : Fin n) :
    Rho5.PivotReindex.remainingIndex (r p) (remainingPerm r p i)
      = r (Rho5.PivotReindex.remainingIndex p i) := by
  have h : Rho5.PivotReindex.remainingEquiv (r p) (remainingPerm r p i)
      = subtypePerm r p (Rho5.PivotReindex.remainingEquiv p i) := by
    simp only [remainingPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  simpa only [Rho5.PivotReindex.remainingEquiv_apply_val] using congrArg Subtype.val h

/-- The inverse reading of the defining property: the remaining index of the source
is the `r.symm`-image of the remaining index of the target. -/
theorem remainingIndex_remainingPerm_symm {n : ℕ} (r : Equiv.Perm (Fin (n + 1)))
    (p : Fin (n + 1)) (i : Fin n) :
    r.symm (Rho5.PivotReindex.remainingIndex (r p) i)
      = Rho5.PivotReindex.remainingIndex p ((remainingPerm r p).symm i) := by
  have h := remainingIndex_remainingPerm r p ((remainingPerm r p).symm i)
  rw [Equiv.apply_symm_apply] at h
  simpa using congrArg (fun x => r.symm x) h

end Rho5.TracePermutation
