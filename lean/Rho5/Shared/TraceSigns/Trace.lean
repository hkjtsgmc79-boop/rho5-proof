/-
D22 — the frozen Schur step and the whole legal trace under row/column sign flips
=================================================================================

* **Goal 2**: the frozen D10 `pivotSchur` of the signed matrix is the frozen Schur
  of the original matrix with the *remaining* row/column signs applied, inherited
  through the original `remainingIndex` map (`pivotSchur_signedEntries`,
  `signedEntries_pivotSchur`).
* **Goal 3**: `legalTrace_signed_iff` — for **every** list of values,
  `LegalTrace (signedEntries A r c) values ↔ LegalTrace A values`.  Both sides
  carry the same value list, so tied pivots, the zero early stop and the exact
  recorded pivot absolute values are all covered.  The reverse direction is the
  forward direction applied to the inverse sign flip (`signedEntries_involutive_inv`).

The matrix is an *index* of `LegalTrace`, so `induction h` cannot form its motive;
the forward direction therefore recurses on the order `n`.  Row and column
**permutations** are a different transformation and belong to D20.
-/
import Rho5.Shared.TraceSigns.Definitions

namespace Rho5.TraceSigns

open Rho5

/-! ## 3. The frozen Schur step -/

/-- **Goal 2.**  The frozen D10 `pivotSchur` of the signed matrix is the frozen
Schur of the original matrix with the *remaining* row and column signs applied.
The remaining signs are inherited through the original `remainingIndex` map:
row `i` of the update carries `r (remainingIndex p i)` and column `j` carries
`c (remainingIndex q j)`.

Interpreted as an elimination step this needs `A p q ≠ 0`, which is exactly how
the trace relation uses it. -/
theorem pivotSchur_signedEntries {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {r c : Fin (n + 1) → ℝ} (hr : IsSign r) (hc : IsSign c)
    (p q : Fin (n + 1)) (hA : A p q ≠ 0) :
    Rho5.PivotReindex.pivotSchur (signedEntries A r c) p q =
      signedEntries (Rho5.PivotReindex.pivotSchur A p q)
        (fun i => r (Rho5.PivotReindex.remainingIndex p i))
        (fun j => c (Rho5.PivotReindex.remainingIndex q j)) := by
  funext i j
  rw [Rho5.PivotReindex.pivotSchur_apply]
  have hR := Rho5.PivotReindex.pivotSchur_apply A p q i j
  rw [show signedEntries (Rho5.PivotReindex.pivotSchur A p q)
        (fun i => r (Rho5.PivotReindex.remainingIndex p i))
        (fun j => c (Rho5.PivotReindex.remainingIndex q j)) i j
      = r (Rho5.PivotReindex.remainingIndex p i) *
          Rho5.PivotReindex.pivotSchur A p q i j *
          c (Rho5.PivotReindex.remainingIndex q j) from rfl]
  rw [hR]
  simp only [signedEntries_apply]
  have hrp : r p ≠ 0 := hr.ne_zero p
  have hcq : c q ≠ 0 := hc.ne_zero q
  have hRi : r p ^ 2 = 1 := by rw [pow_two]; exact hr.mul_self p
  have hCj : c q ^ 2 = 1 := by rw [pow_two]; exact hc.mul_self q
  have hden : r p * A p q * c q ≠ 0 := mul_ne_zero (mul_ne_zero hrp hA) hcq
  field_simp

/-- The same statement in the composition orientation of the remaining signs. -/
theorem signedEntries_pivotSchur {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {r c : Fin (n + 1) → ℝ} (hr : IsSign r) (hc : IsSign c)
    (p q : Fin (n + 1)) (hA : A p q ≠ 0) :
    Rho5.PivotReindex.pivotSchur (signedEntries A r c) p q =
      signedEntries (Rho5.PivotReindex.pivotSchur A p q)
        (r ∘ Rho5.PivotReindex.remainingIndex p)
        (c ∘ Rho5.PivotReindex.remainingIndex q) :=
  pivotSchur_signedEntries A hr hc p q hA

/-! ## 4. The whole legal trace -/

/-- Forward direction of Goal 3 in the general form the recursion uses: a trace of
`B = signedEntries A r c` is a trace of `A` with the same value list. -/
theorem legalTrace_of_signed_of_eq {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    {r c : Fin n → ℝ} (hr : IsSign r) (hc : IsSign c) (hB : B = signedEntries A r c)
    {values : List ℝ} (h : Rho5.CompletePivotPath.LegalTrace B values) :
    Rho5.CompletePivotPath.LegalTrace A values := by
  induction n generalizing values with
  | zero =>
      have h0 : values = [] := by
        cases h with
        | empty => rfl
      subst h0
      have hA0 : A = 0 := by
        funext i j
        exact Fin.elim0 i
      rw [hA0]
      exact Rho5.CompletePivotPath.LegalTrace.empty
  | succ m ih =>
      cases h with
      | zeroStop hzero =>
          have hA0 : A = 0 :=
            (signedEntries_eq_zero_iff' A hr hc).mp (hB ▸ hzero)
          rw [hA0]
          exact Rho5.CompletePivotPath.LegalTrace.zeroStop rfl
      | step p q hmax hne htail =>
          have hmaxS : Rho5.Pivot.IsCompletePivot (signedEntries A r c) p q := by
            rw [← hB]; exact hmax
          have hneS : signedEntries A r c p q ≠ 0 := by
            rw [← hB]; exact hne
          have hmax' : Rho5.Pivot.IsCompletePivot A p q :=
            (isCompletePivot_signedEntries_iff A hr hc p q).mp hmaxS
          have hne' : A p q ≠ 0 :=
            fun h0 => hneS ((signedEntries_eq_zero_iff A hr hc p q).mpr h0)
          have hschur : Rho5.PivotReindex.pivotSchur (signedEntries A r c) p q =
              signedEntries (Rho5.PivotReindex.pivotSchur A p q)
                (fun i => r (Rho5.PivotReindex.remainingIndex p i))
                (fun j => c (Rho5.PivotReindex.remainingIndex q j)) :=
            pivotSchur_signedEntries A hr hc p q hne'
          have htail' : Rho5.CompletePivotPath.LegalTrace
              (Rho5.PivotReindex.pivotSchur A p q) _ :=
            ih (hr := hr.comp_remaining p) (hc := hc.comp_remaining q)
              hschur (by rw [← hB]; exact htail)
          have hBq : B p q = signedEntries A r c p q :=
            congrArg (fun M => M p q) hB
          have habs : |A p q| = |signedEntries A r c p q| :=
            (abs_pivot_signedEntries A hr hc p q).symm
          have habsB : |B p q| = |A p q| := by rw [hBq, habs]
          rw [habsB]
          exact Rho5.CompletePivotPath.LegalTrace.step p q hmax' hne' htail'

/-- Forward direction of Goal 3 in the concrete form: a trace of the signed matrix
is a trace of the original matrix with the same value list. -/
theorem legalTrace_of_signed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {r c : Fin n → ℝ} (hr : IsSign r) (hc : IsSign c) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace (signedEntries A r c) values) :
    Rho5.CompletePivotPath.LegalTrace A values :=
  legalTrace_of_signed_of_eq hr hc rfl h

/-- **Goal 3 (the fixed public lemma).**  Invariance of the *entire* legal-trace
relation under a row/column `±1` sign flip, for every list of values.  The reverse
direction is the forward direction applied to the inverse sign flip, so both sides
carry literally the same value list. -/
theorem legalTrace_signed_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {r c : Fin n → ℝ} (h : IsSign r ∧ IsSign c) (values : List ℝ) :
    Rho5.CompletePivotPath.LegalTrace (signedEntries A r c) values ↔
      Rho5.CompletePivotPath.LegalTrace A values := by
  obtain ⟨hr, hc⟩ := h
  refine ⟨legalTrace_of_signed A hr hc, fun hA => ?_⟩
  have hrc : IsSign fun i => (r i)⁻¹ := hr.inv
  have hcc : IsSign fun j => (c j)⁻¹ := hc.inv
  have hback : A = signedEntries (signedEntries A r c) (fun i => (r i)⁻¹)
      (fun j => (c j)⁻¹) :=
    (signedEntries_involutive_inv A hr hc).symm
  exact legalTrace_of_signed (signedEntries A r c) hrc hcc (by
    rw [← hback]
    exact hA)

/-- The same lemma with the two sign conditions as separate hypotheses. -/
theorem legalTrace_signed_iff' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {r c : Fin n → ℝ} (hr : IsSign r) (hc : IsSign c) (values : List ℝ) :
    Rho5.CompletePivotPath.LegalTrace (signedEntries A r c) values ↔
      Rho5.CompletePivotPath.LegalTrace A values :=
  legalTrace_signed_iff A ⟨hr, hc⟩ values

end Rho5.TraceSigns
