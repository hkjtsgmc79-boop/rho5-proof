/-
D35 — 补零保持峰值：与 `List.ofFn` 向量和 D17 增长值的精确等价
================================================================

**卡目标 4.** 补零**不改变**真实峰值，因此

* 定长 `n` 向量 `List.ofFn v` 的补零轨迹峰值集合 = 原合法路径的峰值集合
  （两个方向都真证明）；
* `growthRatio` 只通过**同一个分母**（`matrixEntryMax A`）搬运，`GrowthValues` 的定义
  一个字也不改：由补零轨迹实现的增长值集合仍等于 D17 的 `GrowthValues`。

关键引理都是关于 `foldr max 0` 的显式计算：

* `tracePeak_append`：`tracePeak (a ++ b) = max (tracePeak a) (tracePeak b)`；
* `tracePeak_replicate_zero`：`tracePeak (replicate k 0) = 0`；
* 于是 `tracePeak (padList n values) = tracePeak values`（用 `tracePeak ≥ 0`）。
-/
import Rho5.Shared.PaddedTrace.Bridge
import Rho5.Shared.GrowthModel

namespace Rho5.PaddedTrace

open Rho5 Rho5.GrowthModel

/-- 辅助：`foldr max` 的起点非负时可以提到 `max` 外面。 -/
theorem foldr_max_eq_max : ∀ (l : List ℝ) {c : ℝ}, 0 ≤ c →
    l.foldr max c = max (l.foldr max 0) c
  | [], c, hc => by
      show c = max 0 c
      rw [max_eq_right hc]
  | a :: t, c, hc => by
      show max a (t.foldr max c) = max (max a (t.foldr max 0)) c
      rw [foldr_max_eq_max t hc, max_assoc]

/-- 峰值对列表拼接可加（取 `max`）。 -/
theorem tracePeak_append (a b : List ℝ) :
    tracePeak (a ++ b) = max (tracePeak a) (tracePeak b) := by
  unfold tracePeak
  rw [List.foldr_append]
  exact foldr_max_eq_max a (by simpa [tracePeak] using tracePeak_nonneg b)

/-- `replicate k 0` 的峰值是 `0`。 -/
theorem tracePeak_replicate_zero : ∀ k : ℕ, tracePeak (List.replicate k 0) = 0
  | 0 => rfl
  | k + 1 => by
      rw [List.replicate_succ, tracePeak_cons, tracePeak_replicate_zero k]
      simp

/-- **卡目标 4（补零保持峰值）**：补零**不改变**峰值——对任意 `n` 与任意列表都成立
（补上的 `replicate _ 0` 的峰值为 `0`，而 `tracePeak ≥ 0`），因此不需要长度假设。 -/
theorem tracePeak_padList {n : ℕ} {values : List ℝ} :
    tracePeak (padList n values) = tracePeak values := by
  unfold padList
  rw [tracePeak_append, tracePeak_replicate_zero, max_eq_left (tracePeak_nonneg values)]

/-- **卡目标 4（逐轨迹形式）**：补零轨迹的峰值等于某条原合法轨迹的峰值。 -/
theorem exists_legalTrace_peak_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {padded : List ℝ}
    (h : PaddedLegalTrace A padded) :
    ∃ values : List ℝ,
      Rho5.CompletePivotPath.LegalTrace A values ∧ tracePeak padded = tracePeak values := by
  obtain ⟨values, hvalues, hpad⟩ := exists_legalTrace_of_padded h
  exact ⟨values, hvalues, by
    rw [hpad, tracePeak_padList]⟩

/-- **卡目标 4（集合等价，列表形式）**：补零轨迹的峰值集合 = 原合法路径的峰值集合。 -/
theorem paddedPeakSet_eq_legalPeakSet {n : ℕ} :
    {p : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℝ, ∃ padded : List ℝ,
        PaddedLegalTrace A padded ∧ p = tracePeak padded}
      = {p : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℝ, ∃ values : List ℝ,
        Rho5.CompletePivotPath.LegalTrace A values ∧ p = tracePeak values} := by
  ext p
  constructor
  · rintro ⟨A, padded, hp, rfl⟩
    obtain ⟨values, hvalues, hpeak⟩ := exists_legalTrace_peak_eq hp
    exact ⟨A, values, hvalues, hpeak⟩
  · rintro ⟨A, values, hvalues, rfl⟩
    exact ⟨A, padList n values, padded_of_legalTrace hvalues, tracePeak_padList.symm⟩

/-- `List.ofFn` 往返：长度匹配时，按 `get` 读回的向量重新 `ofFn` 还原列表。 -/
theorem ofFn_get_eq {l : List ℝ} {n : ℕ} (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.get (Fin.cast h.symm i)) = l := by
  apply List.ext_get
  · rw [List.length_ofFn, h]
  · intro i h1 h2
    rw [List.get_ofFn]
    exact congrArg l.get (Fin.ext rfl)

/-- **卡目标 4（集合等价，`List.ofFn` 向量形式）**：固定 `n` 维向量的补零轨迹峰值集合
= 原合法路径的峰值集合。 -/
theorem paddedVectorPeakSet_eq_legalPeakSet {n : ℕ} :
    {p : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℝ, ∃ v : Fin n → ℝ,
        PaddedLegalTrace A (List.ofFn v) ∧ p = tracePeak (List.ofFn v)}
      = {p : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℝ, ∃ values : List ℝ,
        Rho5.CompletePivotPath.LegalTrace A values ∧ p = tracePeak values} := by
  ext p
  constructor
  · rintro ⟨A, v, hp, rfl⟩
    obtain ⟨values, hvalues, hpeak⟩ := exists_legalTrace_peak_eq hp
    exact ⟨A, values, hvalues, hpeak⟩
  · rintro ⟨A, values, hvalues, rfl⟩
    have hlen : (padList n values).length = n :=
      padList_length (Rho5.CompletePivotPath.length_le hvalues)
    refine ⟨A, fun i : Fin n => (padList n values).get (Fin.cast hlen.symm i), ?_, ?_⟩
    · rw [ofFn_get_eq hlen]
      exact padded_of_legalTrace hvalues
    · rw [ofFn_get_eq hlen]
      exact tracePeak_padList.symm

/-- **卡目标 4（增长值，逐轨迹）**：`Matrix5` 的补零轨迹增长比等于某条原轨迹的增长比
（分母 `matrixEntryMax A` 完全相同，`growthRatio` 的定义未被改动）。 -/
theorem exists_legalTrace_growthRatio_eq {A : Matrix5} {padded : List ℝ}
    (h : PaddedLegalTrace A padded) :
    ∃ values : List ℝ, Rho5.CompletePivotPath.LegalTrace A values
      ∧ growthRatio A padded = growthRatio A values := by
  obtain ⟨values, hvalues, hpad⟩ := exists_legalTrace_of_padded h
  exact ⟨values, hvalues, by
    unfold growthRatio
    rw [hpad, tracePeak_padList]⟩

/-- **卡目标 4（`Matrix5` 增长值集合不变）**：由补零轨迹实现的增长值集合仍等于 D17 的
`GrowthValues`（分母相同，定义未改）。 -/
theorem paddedGrowthValues_eq_growthValues :
    {g : ℝ | ∃ A : Matrix5, ∃ padded : List ℝ,
        A ≠ 0 ∧ PaddedLegalTrace A padded ∧ g = growthRatio A padded}
      = GrowthValues := by
  ext g
  constructor
  · rintro ⟨A, padded, hA, hp, rfl⟩
    obtain ⟨values, hvalues, hpad⟩ := exists_legalTrace_of_padded hp
    refine ⟨A, values, hA, hvalues, ?_⟩
    unfold growthRatio
    rw [hpad, tracePeak_padList]
  · rintro ⟨A, values, hA, hvalues, rfl⟩
    refine ⟨A, padList 5 values, hA, padded_of_legalTrace hvalues, ?_⟩
    unfold growthRatio
    rw [tracePeak_padList]

/-- **卡目标 4（`Matrix5` 逐轨迹增长比）**：`Matrix5` 的补零轨迹与原轨迹增长比相等。 -/
theorem growthRatio_padList {A : Matrix5} {values : List ℝ} :
    growthRatio A (padList 5 values) = growthRatio A values := by
  unfold growthRatio
  rw [tracePeak_padList]

end Rho5.PaddedTrace
