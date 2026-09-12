/-
D22 growth adapter — the actual growth ratio is invariant under row/column `±1`
sign flips
=============================================================================

The frozen D17 growth model attaches to a `Matrix5` and one of its legal traces the
*actual* growth ratio

  `growthRatio A values = tracePeak values / matrixEntryMax A`

(`Rho5.GrowthModel.growthRatio`, reused unchanged).  This module proves that a
row/column sign flip — `signedEntries5 A r c` with every `r i`, `c j` equal to `±1`
(`Rho5.TraceSigns.IsSign`) — leaves that growth ratio, and the associated normalised
and global objects, unchanged:

* `growthRatio_signedEntries5` — `growthRatio (signedEntries5 A r c) values = growthRatio A values`,
  for the **same** value list: no rescaling of the trace is needed because a sign flip
  changes no absolute value;
* `growthRatio_signedEntries5_iff` — the corresponding `↔` for "the trace of the signed
  matrix has growth ratio `g`";
* `mem_growthValues_iff_signed` — membership in D17's frozen `GrowthValues` set is
  invariant under sign flips, in both directions;
* `mem_normalizedGrowthValues_iff_signed` — the same for the frozen
  `NormalizedGrowthValues` set (unit entry-maximum), using the `matrixEntryMax`
  invariance of the flip;
* `bound_signed_iff` — the global bound statement `∀ A values, A ≠ 0 → LegalTrace A values
  → growthRatio A values ≤ B` is invariant, and the analogous statement on D17's frozen
  `GrowthValues` set;
* `bound_normalized_signed_iff` — the same for the normalised form
  `matrixEntryMax A = 1 → tracePeak values ≤ B` and for `NormalizedGrowthValues`.

Nothing here redefines a D17 object: `growthRatio`, `tracePeak`, `GrowthValues` and
`NormalizedGrowthValues` are imported and reused verbatim.  The two ingredients are
D22's own frozen-core results `matrixEntryMax_signedEntries5` and
`legalTrace_signed_iff`.

Scope (frozen by the continuation card): no new canonical-form search, no row/column
permutation (D20's transformation), no generalised scaling, no `sSup`/optimality or
attainment statement, and no re-audit of the D17 growth model.
-/
import Rho5.Shared.GrowthModel
import Rho5.Shared.TraceSigns.Normalize

namespace Rho5.TraceSigns

open Rho5

/-! ## 1. The growth ratio of a sign-flipped matrix -/

/-- **Main statement.**  A row/column `±1` sign flip leaves the actual growth ratio of
any legal trace unchanged — for *the same* trace: a flip changes no absolute value, so
neither the peak `tracePeak values` nor the denominator `matrixEntryMax` moves.

The hypotheses `A ≠ 0` and `LegalTrace A values` are carried exactly as D17's own
statements carry them; the trace of the flipped matrix is produced by
`legalTrace_signed_iff`, not assumed. -/
theorem growthRatio_signedEntries5 {A : Matrix5} {r c : Fin 5 → ℝ}
    (hr : IsSign r) (hc : IsSign c) (values : List ℝ) :
    Rho5.GrowthModel.growthRatio (signedEntries5 A r c) values =
      Rho5.GrowthModel.growthRatio A values := by
  rw [Rho5.GrowthModel.growthRatio_eq, Rho5.GrowthModel.growthRatio_eq,
    matrixEntryMax_signedEntries5 A hr hc]

/-- The `↔` form used by set-level statements: "the trace `values` has growth ratio `g`
for the flipped matrix" is equivalent to the same statement for the original matrix.
Both directions use `legalTrace_signed_iff`. -/
theorem growthRatio_signedEntries5_iff {A : Matrix5} {r c : Fin 5 → ℝ}
    (hr : IsSign r) (hc : IsSign c) {values : List ℝ} {g : ℝ} :
    (Rho5.CompletePivotPath.LegalTrace (signedEntries5 A r c) values ∧
        Rho5.GrowthModel.growthRatio (signedEntries5 A r c) values = g) ↔
      (Rho5.CompletePivotPath.LegalTrace A values ∧
        Rho5.GrowthModel.growthRatio A values = g) := by
  have ht := legalTrace_signed_iff' A hr hc values
  constructor
  · rintro ⟨htr, hg⟩
    exact ⟨ht.mp htr, by rw [← growthRatio_signedEntries5 hr hc values]; exact hg⟩
  · rintro ⟨htr, hg⟩
    exact ⟨ht.mpr htr, by rw [growthRatio_signedEntries5 hr hc values]; exact hg⟩

/-- `signedEntries5` is `signedEntries` at `n = 5`; recorded so the core lemmas apply
directly. -/
theorem signedEntries5_eq_signedEntries' (A : Matrix5) (r c : Fin 5 → ℝ) :
    signedEntries5 A r c = signedEntries A r c := rfl

/-! ## 2. D17's frozen growth-value sets -/

/-- **`GrowthValues` invariance.**  Membership in D17's frozen set of actual growth
values is unchanged by a row/column `±1` sign flip, in both directions: the flip is a
bijection on the set of (matrix, trace) pairs that generate it.

The reverse direction applies the forward statement to the inverse flip
(`IsSign.inv`), so no path existence or uniqueness is assumed. -/
theorem mem_growthValues_iff_signed {g : ℝ} {r c : Fin 5 → ℝ}
    (hr : IsSign r) (hc : IsSign c) :
    g ∈ Rho5.GrowthModel.GrowthValues ↔
      ∃ (A : Matrix5) (values : List ℝ), A ≠ 0 ∧
        Rho5.CompletePivotPath.LegalTrace (signedEntries5 A r c) values ∧
        g = Rho5.GrowthModel.growthRatio (signedEntries5 A r c) values := by
  constructor
  · rintro ⟨A, values, hA, htrace, hg⟩
    refine ⟨A, values, hA, (legalTrace_signed_iff' A hr hc values).mpr htrace, ?_⟩
    rw [growthRatio_signedEntries5 hr hc values]
    exact hg
  · rintro ⟨A, values, hA, htrace, hg⟩
    have htr : Rho5.CompletePivotPath.LegalTrace A values :=
      (legalTrace_signed_iff' A hr hc values).mp htrace
    refine ⟨A, values, hA, htr, ?_⟩
    have hflip : Rho5.GrowthModel.growthRatio (signedEntries5 A r c) values =
        Rho5.GrowthModel.growthRatio A values := growthRatio_signedEntries5 hr hc values
    rw [← hflip]
    exact hg

/-- The same invariance stated as equality of the existentially quantified predicate,
i.e. flipping every matrix in the generating family does not change the set. -/
theorem growthValues_signed_eq {r c : Fin 5 → ℝ} (hr : IsSign r) (hc : IsSign c) :
    {g : ℝ | ∃ (A : Matrix5) (values : List ℝ), A ≠ 0 ∧
        Rho5.CompletePivotPath.LegalTrace (signedEntries5 A r c) values ∧
        g = Rho5.GrowthModel.growthRatio (signedEntries5 A r c) values} =
      Rho5.GrowthModel.GrowthValues := by
  ext g
  exact (mem_growthValues_iff_signed hr hc).symm

/-- **`NormalizedGrowthValues` invariance.**  Membership in D17's frozen unit-normalised
set is likewise unchanged: the flip preserves `matrixEntryMax = 1` (via the entry-max
invariance) and `tracePeak values` is untouched because no absolute value moves. -/
theorem mem_normalizedGrowthValues_iff_signed {g : ℝ} {r c : Fin 5 → ℝ}
    (hr : IsSign r) (hc : IsSign c) :
    g ∈ Rho5.GrowthModel.NormalizedGrowthValues ↔
      ∃ (A : Matrix5) (values : List ℝ), matrixEntryMax (signedEntries5 A r c) = 1 ∧
        Rho5.CompletePivotPath.LegalTrace (signedEntries5 A r c) values ∧
        g = Rho5.GrowthModel.tracePeak values := by
  constructor
  · rintro ⟨A, values, hmax, htrace, hg⟩
    refine ⟨A, values, ?_, (legalTrace_signed_iff' A hr hc values).mpr htrace, hg⟩
    rw [matrixEntryMax_signedEntries5 A hr hc]
    exact hmax
  · rintro ⟨A, values, hmax, htrace, hg⟩
    refine ⟨A, values, ?_, (legalTrace_signed_iff' A hr hc values).mp htrace, hg⟩
    rw [matrixEntryMax_signedEntries5 A hr hc] at hmax
    exact hmax

/-! ## 3. Global bound statements -/

/-- A `Matrix5` is zero exactly when its sign flip is. -/
theorem signedEntries5_eq_zero_iff (A : Matrix5) {r c : Fin 5 → ℝ}
    (hr : IsSign r) (hc : IsSign c) : signedEntries5 A r c = 0 ↔ A = 0 := by
  rw [signedEntries5_eq_signedEntries']
  exact signedEntries_eq_zero_iff' A hr hc

/-- A sign flip of a nonzero matrix is nonzero. -/
theorem signedEntries5_ne_zero_of_ne_zero {A : Matrix5} {r c : Fin 5 → ℝ}
    (hr : IsSign r) (hc : IsSign c) (hA : A ≠ 0) : signedEntries5 A r c ≠ 0 :=
  fun h0 => hA ((signedEntries5_eq_zero_iff A hr hc).mp h0)

/-- A sign flip that is nonzero comes from a nonzero matrix. -/
theorem ne_zero_of_signedEntries5_ne_zero {A : Matrix5} {r c : Fin 5 → ℝ}
    (hr : IsSign r) (hc : IsSign c) (hA : signedEntries5 A r c ≠ 0) : A ≠ 0 :=
  fun h0 => hA ((signedEntries5_eq_zero_iff A hr hc).mpr h0)

/-- **Global ratio bound invariance.**  For any `B`, "every legal trace of every nonzero
`Matrix5` has growth ratio at most `B`" is equivalent to the same statement with every
matrix replaced by a `±1` row/column sign flip of it. -/

theorem bound_signed_iff (B : ℝ) {r c : Fin 5 → ℝ} (hr : IsSign r) (hc : IsSign c) :
    (∀ (A : Matrix5) (values : List ℝ), A ≠ 0 →
        Rho5.CompletePivotPath.LegalTrace (signedEntries5 A r c) values →
        Rho5.GrowthModel.growthRatio (signedEntries5 A r c) values ≤ B) ↔
      (∀ (A : Matrix5) (values : List ℝ), A ≠ 0 →
        Rho5.CompletePivotPath.LegalTrace A values →
        Rho5.GrowthModel.growthRatio A values ≤ B) := by
  constructor
  · intro h A values hA htr
    have hb := h A values hA ((legalTrace_signed_iff' A hr hc values).mpr htr)
    rwa [growthRatio_signedEntries5 hr hc values] at hb
  · intro h A values hA htr
    have hb := h A values hA ((legalTrace_signed_iff' A hr hc values).mp htr)
    rwa [← growthRatio_signedEntries5 hr hc values] at hb

/-- **Global bound invariance on D17's frozen set.**  `B` bounds every element of
`GrowthValues` exactly when it bounds every growth ratio of a sign-flipped matrix. -/
theorem bound_growthValues_signed_iff (B : ℝ) {r c : Fin 5 → ℝ}
    (hr : IsSign r) (hc : IsSign c) :
    (∀ g ∈ Rho5.GrowthModel.GrowthValues, g ≤ B) ↔
      (∀ g : ℝ, (∃ (A : Matrix5) (values : List ℝ), A ≠ 0 ∧
          Rho5.CompletePivotPath.LegalTrace (signedEntries5 A r c) values ∧
          g = Rho5.GrowthModel.growthRatio (signedEntries5 A r c) values) → g ≤ B) := by
  simp only [mem_growthValues_iff_signed (g := _) hr hc]

/-- **Normalised global bound invariance.**  The same for the normalised form used by
D17's certificate interface: `matrixEntryMax A = 1 → tracePeak values ≤ B`.  As in
D17, `A ≠ 0` is carried explicitly alongside the unit entry-maximum hypothesis. -/
theorem bound_normalized_signed_iff (B : ℝ) {r c : Fin 5 → ℝ}
    (hr : IsSign r) (hc : IsSign c) :
    (∀ (A : Matrix5) (values : List ℝ), A ≠ 0 →
        matrixEntryMax (signedEntries5 A r c) = 1 →
        Rho5.CompletePivotPath.LegalTrace (signedEntries5 A r c) values →
        Rho5.GrowthModel.tracePeak values ≤ B) ↔
      (∀ (A : Matrix5) (values : List ℝ), A ≠ 0 → matrixEntryMax A = 1 →
        Rho5.CompletePivotPath.LegalTrace A values →
        Rho5.GrowthModel.tracePeak values ≤ B) := by
  constructor
  · intro h A values hA hmaxA htr
    have hmaxS : matrixEntryMax (signedEntries5 A r c) = 1 :=
      (matrixEntryMax_signedEntries5 A hr hc).trans hmaxA
    exact h A values hA hmaxS ((legalTrace_signed_iff' A hr hc values).mpr htr)
  · intro h A values hA hmaxS htr
    have hmaxA : matrixEntryMax A = 1 :=
      (matrixEntryMax_signedEntries5 A hr hc).symm.trans hmaxS
    exact h A values hA hmaxA ((legalTrace_signed_iff' A hr hc values).mp htr)

end Rho5.TraceSigns
