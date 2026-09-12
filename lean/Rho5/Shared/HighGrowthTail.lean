/-
D45 — 高增长只能出现在第四或第五主元：实际路径分支接口
=====================================================

Card purpose: a later global-bound argument must handle *where* the growth peak of a
real `LegalTrace` occurs; it may not silently assume "the last pivot" or full rank.
This file turns D15's already-proved coarse per-stage bound `2^k * M` into a **branch
interface on the real trace**: a genuine `growthRatio > 4` can only peak at the 4th or
5th pivot (0-based indices `3`, `4`), and the matching positive prefix is paid.

Reused read-only (no upstream proof is repeated):
* D15 `Rho5.TraceGrowth.legalTrace_boundBy` — the `2^k * B` per-index bound (this file
  does **not** write that induction again);
* D13 `Rho5.CompletePivotPath.LegalTrace` (`empty`/`zeroStop`/`step`), `length_le`,
  `ne_nil_of_pos`;
* D17 `Rho5.GrowthModel.{tracePeak, growthRatio, growthRatio_eq, length_le_five}`;
* D08 `Rho5.MatrixNormalization.{matrixEntryMax_nonneg, matrixEntryMax_pos,
  abs_entry_le_matrixEntryMax, normalize, matrixEntryMax_normalize, eq_smul_normalize}`.

Semantics preserved exactly: the `zeroStop = [0]` early stop and the 0-based list index
convention ("4th/5th pivot" = index 3/4).  No full-rank hypothesis, no attainability
assumption, no `rho5Trace > 4` claim.  No `sorry`, no `admit`, no project axiom, no
`native_decide`.
-/
import Rho5.Shared.TraceGrowth
import Rho5.Shared.GrowthModel

namespace Rho5.HighGrowthTail

open Rho5

/-! ## 0. The entry maximum `M` and the reused per-index `2^k` interface -/

/-- The entry maximum, kept as an abbreviation of the frozen `matrixEntryMax` so that
every statement below is about the *same* real quantity. -/
noncomputable abbrev M (A : Matrix5) : ℝ := matrixEntryMax A

theorem M_nonneg (A : Matrix5) : 0 ≤ M A :=
  Rho5.MatrixNormalization.matrixEntryMax_nonneg A

theorem M_pos {A : Matrix5} (hA : A ≠ 0) : 0 < M A :=
  Rho5.MatrixNormalization.matrixEntryMax_pos A hA

theorem abs_entry_le_M (A : Matrix5) (i j : Fin 5) : |A i j| ≤ M A :=
  Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax A i j

/-- **Reused D15 bound.** The `k`-th recorded value of any legal trace of `A` is at
most `2^k * M A`.  This is D15's `legalTrace_boundBy` instantiated at the entry bound;
the `2^k` induction itself lives upstream and is not re-proved here. -/
theorem values_get_le_pow (A : Matrix5) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) (k : Fin values.length) :
    values.get k ≤ (2 : ℝ) ^ (k : ℕ) * M A :=
  Rho5.TraceGrowth.legalTrace_boundBy h (abs_entry_le_M A) k

/-! ## 1. Card item 1: the first three recorded values are `≤ M`, `2M`, `4M`

Corollaries of the reused stagewise bound at indices `0`, `1`, `2`.  Early stop is
inherited unchanged: for a zero matrix the trace is `[0]`, where the indices `≥ 1` do
not exist and the statements are vacuous. -/

/-- **Item 1 (first value).** The first recorded value is at most `M A`. -/
theorem first_value_le_M (A : Matrix5) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) (k : Fin values.length)
    (hk : (k : ℕ) = 0) : values.get k ≤ M A := by
  have hb := values_get_le_pow A h k
  rw [hk] at hb
  norm_num at hb
  exact hb

/-- **Item 1 (second value).** The second recorded value is at most `2 * M A`. -/
theorem second_value_le_two_M (A : Matrix5) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) (k : Fin values.length)
    (hk : (k : ℕ) = 1) : values.get k ≤ 2 * M A := by
  have hb := values_get_le_pow A h k
  rw [hk] at hb
  norm_num at hb
  exact hb

/-- **Item 1 (third value).** The third recorded value is at most `4 * M A`. -/
theorem third_value_le_four_M (A : Matrix5) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) (k : Fin values.length)
    (hk : (k : ℕ) = 2) : values.get k ≤ 4 * M A := by
  have hb := values_get_le_pow A h k
  rw [hk] at hb
  norm_num at hb
  exact hb

/-- **Item 1 (packaged).** The three bounds at once, in the shape a downstream case
analysis consumes. -/
theorem first_three_le (A : Matrix5) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) :
    (∀ k : Fin values.length, (k : ℕ) = 0 → values.get k ≤ M A) ∧
      (∀ k : Fin values.length, (k : ℕ) = 1 → values.get k ≤ 2 * M A) ∧
      (∀ k : Fin values.length, (k : ℕ) = 2 → values.get k ≤ 4 * M A) :=
  ⟨fun k hk => first_value_le_M A h k hk,
   fun k hk => second_value_le_two_M A h k hk,
   fun k hk => third_value_le_four_M A h k hk⟩

/-- **Item 1 (uniform form used below).** Every index `k < 3` (i.e. the first three
pivots) satisfies `values.get k ≤ 4 * M A`.  Obtained from the reused `2^k` bound with
`2^k ≤ 2^2 = 4`; this is the form the index restriction of item 2 consumes. -/
theorem value_le_four_M_of_lt_three (A : Matrix5) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) (k : Fin values.length)
    (hk : (k : ℕ) < 3) : values.get k ≤ 4 * M A := by
  have hb := values_get_le_pow A h k
  have hpow : (2 : ℝ) ^ (k : ℕ) ≤ 4 := by
    have hk2 : (k : ℕ) ≤ 2 := Nat.le_of_lt_succ hk
    calc (2 : ℝ) ^ (k : ℕ) ≤ (2 : ℝ) ^ 2 := pow_le_pow_right₀ (by norm_num) hk2
      _ = 4 := by norm_num
  calc values.get k ≤ (2 : ℝ) ^ (k : ℕ) * M A := hb
    _ ≤ 4 * M A := mul_le_mul_of_nonneg_right hpow (M_nonneg A)

/-! ## 2. Attainment of the peak (list-level, no model content) -/

/-- The peak `tracePeak values` of a nonempty list of *nonnegative* reals is attained
by one of its entries.  (`tracePeak` folds `max` from the right starting at `0`, so
attainment needs the entries to be `≥ 0`; for a `LegalTrace` this is D13's `nonneg`.)
Proved by structural recursion on the list; this is what lets item 2 produce a *real*
index witness instead of assuming a tail peak. -/
theorem exists_mem_eq_tracePeak : ∀ (values : List ℝ), (∀ v ∈ values, 0 ≤ v) →
    values ≠ [] → ∃ v ∈ values, v = Rho5.GrowthModel.tracePeak values
  | [], _, h => absurd rfl h
  | a :: t, hnn, _ => by
      rcases eq_or_ne t [] with rfl | ht
      · refine ⟨a, by simp, ?_⟩
        have ha : 0 ≤ a := hnn a (by simp)
        exact (max_eq_left ha).symm
      · have hnn' : ∀ v ∈ t, 0 ≤ v := fun v hv => hnn v (by simp [hv])
        obtain ⟨v, hv, hve⟩ := exists_mem_eq_tracePeak t hnn' ht
        rcases le_total a v with hav | hva
        · refine ⟨v, by simp [hv], ?_⟩
          have hav' : a ≤ Rho5.GrowthModel.tracePeak t := by rw [← hve]; exact hav
          rw [hve]
          exact (max_eq_right hav').symm
        · refine ⟨a, by simp, ?_⟩
          have ht_le : Rho5.GrowthModel.tracePeak t ≤ a := by rw [← hve]; exact hva
          exact (max_eq_left ht_le).symm

/-! ## 3. Card item 2: a growth peak above `4 * M` sits at index 3 or index 4 -/

/-- **Item 2 (main).** For a nonzero `Matrix5` and a real `LegalTrace` whose
`growthRatio` exceeds `4`, the trace has at least four recorded values and its peak is
attained at index `3` (4th pivot) or index `4` (5th pivot), where it strictly exceeds
`4 * M A`.

Both the length lower bound and the index restriction are *derived*: the peak is
attained at a genuine `Fin` index (section 2), indices below `3` are excluded by the
reused `2^k` bound (section 1), and indices `≥ 5` do not exist because a `Matrix5` trace
has length at most `5` (D13 `length_le` through D17 `length_le_five`).  Neither full
rank nor a last-pivot peak is assumed. -/
theorem peak_at_index_three_or_four (A : Matrix5) (hA : A ≠ 0) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio A values) :
    4 ≤ values.length ∧
      ∃ k : Fin values.length, ((k : ℕ) = 3 ∨ (k : ℕ) = 4) ∧
        values.get k = Rho5.GrowthModel.tracePeak values ∧
        4 * M A < values.get k := by
  have hM : 0 < M A := M_pos hA
  -- `growthRatio > 4` is exactly `4 * M A < tracePeak`
  have hpeak_gt : 4 * M A < Rho5.GrowthModel.tracePeak values := by
    have h' : 4 < Rho5.GrowthModel.tracePeak values / M A := by
      rw [Rho5.GrowthModel.growthRatio_eq] at hgrowth
      exact hgrowth
    exact (lt_div_iff₀ hM).mp h'
  -- the trace is nonempty, so the peak has a real index witness
  have hne : values ≠ [] := by
    rintro rfl
    have h0 : Rho5.GrowthModel.tracePeak ([] : List ℝ) = 0 := Rho5.GrowthModel.tracePeak_nil
    linarith
  obtain ⟨v, hv, hve⟩ :=
    exists_mem_eq_tracePeak values (Rho5.CompletePivotPath.nonneg h) hne
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hv
  have hkpeak : values.get k = Rho5.GrowthModel.tracePeak values := hk.trans hve
  have hkgt : 4 * M A < values.get k := by rw [hkpeak]; exact hpeak_gt
  -- index restriction
  have hk_le4 : (k : ℕ) ≤ 4 :=
    Nat.lt_succ_iff.mp
      (lt_of_lt_of_le k.isLt (Rho5.GrowthModel.length_le_five h))
  have hidx : (k : ℕ) = 3 ∨ (k : ℕ) = 4 := by
    rcases lt_or_ge (k : ℕ) 3 with h3 | h3
    · exact absurd (value_le_four_M_of_lt_three A h k h3) (not_le.mpr hkgt)
    · rcases lt_or_eq_of_le hk_le4 with h4 | h4
      · exact Or.inl (le_antisymm (Nat.le_of_lt_succ h4) h3)
      · exact Or.inr h4
  have hlen4 : 4 ≤ values.length := by
    rcases hidx with h3 | h4
    · have hlt := k.isLt
      rw [h3] at hlt
      exact Nat.succ_le_iff.mpr hlt
    · have hlt := k.isLt
      rw [h4] at hlt
      exact le_of_lt hlt
  exact ⟨hlen4, k, hidx, hkpeak, hkgt⟩

/-- `getD` at an in-range index with fallback `0` is the real `get` value.  Stated once
here so that every `getD` statement below is derived, never assumed. -/
theorem getD_eq_get_of_lt {values : List ℝ} {n : ℕ} (hn : n < values.length) :
    values.getD n 0 = values.get ⟨n, hn⟩ :=
  (List.getElem_eq_getD (l := values) (i := n) (h := hn) (0 : ℝ)).symm

/-- **Item 2 (explicit branch with `getD`).** The same witness, additionally expressed
through `getD` at the witness index, with the out-of-range default fixed to `0`. -/
theorem peak_is_getD_at_witness (A : Matrix5) (hA : A ≠ 0) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio A values) :
    ∃ k : Fin values.length, ((k : ℕ) = 3 ∨ (k : ℕ) = 4) ∧
      values.get k = Rho5.GrowthModel.tracePeak values ∧
      values.getD (k : ℕ) 0 = Rho5.GrowthModel.tracePeak values ∧
      4 * M A < values.getD (k : ℕ) 0 := by
  obtain ⟨_, k, hidx, hkpeak, hkgt⟩ := peak_at_index_three_or_four A hA h hgrowth
  have hd : values.getD (k : ℕ) 0 = values.get k :=
    getD_eq_get_of_lt (values := values) (n := (k : ℕ)) k.isLt
  exact ⟨k, hidx, hkpeak, by rw [hd]; exact hkpeak, by rw [hd]; exact hkgt⟩

/-- **Item 2 (the two literal `getD` branches).** The peak equals `values.getD 3 0` with
a real index `3` existing, or `values.getD 4 0` with a real index `4` existing; the
length conjuncts are exactly what makes the default `0` unreachable, and each branch
carries its strict bound. -/
theorem peak_is_getD_three_or_four (A : Matrix5) (hA : A ≠ 0) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio A values) :
    (4 ≤ values.length ∧ values.getD 3 0 = Rho5.GrowthModel.tracePeak values ∧
        4 * M A < values.getD 3 0) ∨
      (5 ≤ values.length ∧ values.getD 4 0 = Rho5.GrowthModel.tracePeak values ∧
        4 * M A < values.getD 4 0) := by
  obtain ⟨hlen, k, hidx, hkpeak, hkgt⟩ := peak_at_index_three_or_four A hA h hgrowth
  rcases hidx with h3 | h4
  · left
    have hk3 : 3 < values.length := by
      have hlt := k.isLt
      rw [h3] at hlt
      exact hlt
    have hfin : (⟨3, hk3⟩ : Fin values.length) = k := Fin.ext h3.symm
    have hget3 : values.get ⟨3, hk3⟩ = Rho5.GrowthModel.tracePeak values := by
      rw [hfin]; exact hkpeak
    have hgt3 : 4 * M A < values.get ⟨3, hk3⟩ := by
      rw [hget3, ← hkpeak]
      exact hkgt
    have hd3 : values.getD 3 0 = values.get ⟨3, hk3⟩ :=
      getD_eq_get_of_lt (values := values) (n := 3) hk3
    exact ⟨hlen, by rw [hd3]; exact hget3, by rw [hd3]; exact hgt3⟩
  · right
    have hk4 : 4 < values.length := by
      have hlt := k.isLt
      rw [h4] at hlt
      exact hlt
    have hfin : (⟨4, hk4⟩ : Fin values.length) = k := Fin.ext h4.symm
    have hget4 : values.get ⟨4, hk4⟩ = Rho5.GrowthModel.tracePeak values := by
      rw [hfin]; exact hkpeak
    have hgt4 : 4 * M A < values.get ⟨4, hk4⟩ := by
      rw [hget4, ← hkpeak]
      exact hkgt
    have hd4 : values.getD 4 0 = values.get ⟨4, hk4⟩ :=
      getD_eq_get_of_lt (values := values) (n := 4) hk4
    exact ⟨Nat.succ_le_iff.mpr hk4, by rw [hd4]; exact hget4, by rw [hd4]; exact hgt4⟩

/-! ## 4. Card item 3: positivity of the real prefix, paid by `LegalTrace` semantics

Every `step` of a `LegalTrace` is a *nonzero* pivot and records its absolute value; the
only way a recorded value can be `0` is the `zeroStop = [0]` terminal.  Hence a strictly
positive valid value at index `k` forces every earlier recorded value to be strictly
positive.  This pays the prefix obligation without any full-rank hypothesis and without
silently reading "length = 5" as "all values nonzero". -/

/-- Auxiliary list step: prepending a positive value preserves prefix positivity. -/
theorem prefix_pos_cons {a : ℝ} (ha : 0 < a) {tail : List ℝ}
    (ih : ∀ (k : ℕ) (hk : k < tail.length), 0 < tail.get ⟨k, hk⟩ →
      ∀ j (hj : j < tail.length), j ≤ k → 0 < tail.get ⟨j, hj⟩) :
    ∀ (k : ℕ) (hk : k < (a :: tail).length), 0 < (a :: tail).get ⟨k, hk⟩ →
      ∀ j (hj : j < (a :: tail).length), j ≤ k → 0 < (a :: tail).get ⟨j, hj⟩ := by
  intro k hk hpos j hj hjk
  cases k with
  | zero =>
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hjk
      subst hj0
      exact ha
  | succ k' =>
      have hk' : k' < tail.length := by simpa using hk
      have hpos' : 0 < tail.get ⟨k', hk'⟩ := by
        rw [List.get_cons_succ] at hpos
        exact hpos
      cases j with
      | zero => exact ha
      | succ j' =>
          have hj' : j' < tail.length := by simpa using hj
          have hle : j' ≤ k' := Nat.le_of_succ_le_succ hjk
          have hres := ih k' hk' hpos' j' hj' hle
          rw [List.get_cons_succ]
          exact hres

/-- **Item 3 (main).** If the valid `k`-th value of a real `LegalTrace` is strictly
positive, then all of the first `k + 1` recorded values are strictly positive. -/
theorem prefix_pos_of_get_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) :
    ∀ (k : ℕ) (hk : k < values.length), 0 < values.get ⟨k, hk⟩ →
      ∀ j (hj : j < values.length), j ≤ k → 0 < values.get ⟨j, hj⟩ := by
  induction h with
  | empty => intro k hk; exact absurd hk (by simp)
  | zeroStop hzero =>
      intro k hk hpos j hj hjk
      have hk0 : k = 0 := Nat.lt_one_iff.mp (by simpa using hk)
      subst hk0
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hjk
      subst hj0
      simp at hpos
  | step p q hmax hne htail ih =>
      exact prefix_pos_cons (abs_pos.mpr hne) ih

/-- **Item 3 (index form).** The same statement with the witness index exposed, for
downstream case analysis. -/
theorem prefix_pos_of_get_pos_at (A : Matrix5) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) {k : ℕ} (hk : k < values.length)
    (hpos : 0 < values.get ⟨k, hk⟩) :
    ∀ j (hj : j < values.length), j ≤ k → 0 < values.get ⟨j, hj⟩ :=
  prefix_pos_of_get_pos h k hk hpos

/-- **Item 3 (branches packaged with item 2).** One witness `k ∈ {3, 4}` carrying the
strict peak bound and the positivity of the whole prefix: four nonzero steps for the
index-`3` branch, all five for the index-`4` branch. -/
theorem peak_branch_with_positive_prefix (A : Matrix5) (hA : A ≠ 0) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio A values) :
    ∃ k : Fin values.length, ((k : ℕ) = 3 ∨ (k : ℕ) = 4) ∧
      values.get k = Rho5.GrowthModel.tracePeak values ∧
      4 * M A < values.get k ∧
      (∀ j (hj : j < values.length), j ≤ (k : ℕ) → 0 < values.get ⟨j, hj⟩) := by
  obtain ⟨_, k, hidx, hkpeak, hkgt⟩ := peak_at_index_three_or_four A hA h hgrowth
  have hM : 0 < M A := M_pos hA
  have h4M : 0 < 4 * M A := by linarith
  have hpos : 0 < values.get k := lt_trans h4M hkgt
  exact ⟨k, hidx, hkpeak, hkgt, prefix_pos_of_get_pos h (k : ℕ) k.isLt hpos⟩

/-! ## 5. Card item 4: the `matrixEntryMax A = 1` adapters -/

/-- The normalization of a nonzero `Matrix5` is nonzero (derived from D08's restoration
identity, not assumed), so section 3 applies to it. -/
theorem normalize_ne_zero (A : Matrix5) (hA : A ≠ 0) :
    Rho5.MatrixNormalization.normalize A ≠ 0 := by
  intro hz
  apply hA
  rw [Rho5.MatrixNormalization.eq_smul_normalize A hA, hz, smul_zero]

/-- **Item 4 (unit maximum form).** With `matrixEntryMax A = 1`, the branch interface
becomes the numeric statement `4 < peak`, directly usable by a downstream argument that
*assumes* `rho5Trace > 4`.  No such inequality is claimed here. -/
theorem peak_at_index_three_or_four_of_M_eq_one (A : Matrix5) (hA : A ≠ 0)
    {values : List ℝ} (h : Rho5.CompletePivotPath.LegalTrace A values) (hM : M A = 1)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio A values) :
    4 ≤ values.length ∧
      ∃ k : Fin values.length, ((k : ℕ) = 3 ∨ (k : ℕ) = 4) ∧
        values.get k = Rho5.GrowthModel.tracePeak values ∧ 4 < values.get k := by
  obtain ⟨hlen, k, hidx, hkpeak, hkgt⟩ := peak_at_index_three_or_four A hA h hgrowth
  refine ⟨hlen, k, hidx, hkpeak, ?_⟩
  rw [hM, mul_one] at hkgt
  exact hkgt

/-- **Item 4 (normalized maximal matrix adapter).** For a nonzero `Matrix5`, the
normalization has entry maximum `1` (D08 `matrixEntryMax_normalize`), so the index-3/4
branch applies to `normalize A` whenever its growth ratio exceeds `4`.  This is the form
a normalized-maximal-matrix argument can call directly. -/
theorem normalize_peak_at_index_three_or_four (A : Matrix5) (hA : A ≠ 0)
    {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace (Rho5.MatrixNormalization.normalize A) values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio (Rho5.MatrixNormalization.normalize A) values) :
    4 ≤ values.length ∧
      ∃ k : Fin values.length, ((k : ℕ) = 3 ∨ (k : ℕ) = 4) ∧
        values.get k = Rho5.GrowthModel.tracePeak values ∧ 4 < values.get k :=
  peak_at_index_three_or_four_of_M_eq_one (Rho5.MatrixNormalization.normalize A)
    (normalize_ne_zero A hA) h (Rho5.MatrixNormalization.matrixEntryMax_normalize A hA)
    hgrowth

end Rho5.HighGrowthTail
