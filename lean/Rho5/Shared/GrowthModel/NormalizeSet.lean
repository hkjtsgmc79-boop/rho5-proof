/-
D17 — 增长值集合、单位归一化集合与二者的等价
============================================

冻结公开接口（D18 组装卡直接消费，名称与语义均固定）：

* `Rho5.GrowthModel.GrowthValues : Set ℝ`
  `= {g | ∃ A values, A ≠ 0 ∧ LegalTrace A values ∧ g = growthRatio A values}`；
* `Rho5.GrowthModel.NormalizedGrowthValues : Set ℝ`
  `= {g | ∃ A values, matrixEntryMax A = 1 ∧ LegalTrace A values ∧ g = tracePeak values}`；
* `Rho5.GrowthModel.growthValues_eq_normalized`（**固定名**）：
  `GrowthValues = NormalizedGrowthValues`；
* `Rho5.GrowthModel.bound_iff_bound_normalized`：对任意 `B`，
  “所有非零矩阵的所有合法轨迹增长比 ≤ B” ⟺
  “所有单位 entry-max 矩阵的所有合法轨迹峰值 ≤ B”。

两向都真的证明，并且**不假定任何一条路径存在、也不假定路径唯一**：每个已有轨迹
只要“可转移”即可（“每个已有轨迹可转移”就是 `growthValues_eq_normalized` 的两个方向
本身）：

* `⊆`（单位化方向）：任取 `A ≠ 0` 与其合法轨迹 `values`，取 `A' := normalize A`。
  D08 给 `matrixEntryMax A' = 1`，D13 的整条轨迹缩放等价
  `legalTrace_normalize_iff` 把这条轨迹变成 `A'` 的合法轨迹并给出峰值等式
  `tracePeak (map (· * (matrixEntryMax A)⁻¹)) = growthRatio A values`
  （`tracePeak_normalize`）。于是 `g = tracePeak (缩放后轨迹)` 是归一化集合的成员。
* `⊇`（反单位化方向）：任取 `matrixEntryMax A = 1` 与合法轨迹，则该假设本身给出
  `A ≠ 0`（`ne_zero_of_matrixEntryMax_eq_one`），且 `growthRatio A values = tracePeak values`
  （分母是 `1`），无需再做任何构造。

**本卡不**定义最终 `rho5` 的上确界、**不**声称集合非空或有界（D14、D15、后继 D18
负责）、**不**把粗界 `16` 冒充 alpha 最优界、**不**证明候选矩阵达到性。这里只交付
集合等式与“任意 `B` 下界命题等价”的接口。

复用（只读冻结输入）：D13 `CompletePivotPath`（`LegalTrace`、`legalTrace_normalize_iff`）、
D08 `MatrixNormalization`（`normalize`、`matrixEntryMax_normalize`、
`matrixEntryMax_eq_zero_iff`、`matrixEntryMax_ne_zero`）。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.GrowthModel.Unit

namespace Rho5.GrowthModel

open Rho5

/-! ## 集合定义（冻结名） -/

/-- **冻结定义（D17 卡）**：实际轨迹增长值集合——所有非零 `Matrix5` 的所有合法轨迹的
`growthRatio` 取值。`A ≠ 0` 与 `LegalTrace A values` 是集合的组成部分，不是外部假设。 -/
def GrowthValues : Set ℝ :=
  {g | ∃ (A : Matrix5) (values : List ℝ),
    A ≠ 0 ∧ Rho5.CompletePivotPath.LegalTrace A values ∧ g = growthRatio A values}

/-- **冻结定义（D17 卡）**：单位归一化增长值集合——所有“元素最大范数 = 1”的矩阵的
所有合法轨迹的**峰值**（不再除分母）。与 `GrowthValues` 的区别只在归一化与“比值 /
峰值”的写法，集合本身（`growthValues_eq_normalized`）相同。 -/
def NormalizedGrowthValues : Set ℝ :=
  {g | ∃ (A : Matrix5) (values : List ℝ),
    matrixEntryMax A = 1 ∧ Rho5.CompletePivotPath.LegalTrace A values ∧ g = tracePeak values}

/-- 成员展开式（`GrowthValues`），后继组装常用的重写入口。 -/
theorem mem_growthValues_iff {g : ℝ} :
    g ∈ GrowthValues ↔ ∃ (A : Matrix5) (values : List ℝ),
      A ≠ 0 ∧ Rho5.CompletePivotPath.LegalTrace A values ∧ g = growthRatio A values :=
  Iff.rfl

/-- 成员展开式（`NormalizedGrowthValues`）。 -/
theorem mem_normalizedGrowthValues_iff {g : ℝ} :
    g ∈ NormalizedGrowthValues ↔ ∃ (A : Matrix5) (values : List ℝ),
      matrixEntryMax A = 1 ∧ Rho5.CompletePivotPath.LegalTrace A values ∧
        g = tracePeak values :=
  Iff.rfl

/-! ## 单位 entry-max 与“非零”的关系（无额外假设） -/

/-- `matrixEntryMax A = 1` 本身蕴含 `A ≠ 0`：集合 `NormalizedGrowthValues` 的成员
定义中已经内含非零性，无需另加前提（D08 的 `matrixEntryMax_eq_zero_iff`）。 -/
theorem ne_zero_of_matrixEntryMax_eq_one {A : Matrix5} (h : matrixEntryMax A = 1) :
    A ≠ 0 := by
  intro h0
  have h1 := (Rho5.MatrixNormalization.matrixEntryMax_eq_zero_iff A).mpr h0
  rw [h] at h1
  exact one_ne_zero h1

/-- 单位 entry-max 的矩阵其增长比就是峰值（分母为 `1`）。 -/
theorem growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one {A : Matrix5} {values : List ℝ}
    (h : matrixEntryMax A = 1) : growthRatio A values = tracePeak values := by
  rw [growthRatio_eq, h, div_one]

/-- 存在单位 entry-max 的非零矩阵（常值 `1` 矩阵）。本引理只为“`NormalizedGrowthValues`
的成员条件可满足”提供显式见证，**不**声称任何集合非空（那属于 D14/D18）。 -/
theorem matrixEntryMax_const_one : matrixEntryMax (fun _ _ : Fin 5 => (1 : ℝ)) = 1 := by
  have hle : matrixEntryMax (fun _ _ : Fin 5 => (1 : ℝ)) ≤ 1 := by
    unfold matrixEntryMax
    refine Finset.sup'_le Finset.univ_nonempty _ (fun ij _ => ?_)
    simp
  have hge : 1 ≤ matrixEntryMax (fun _ _ : Fin 5 => (1 : ℝ)) := by
    have h := Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax
      (fun _ _ : Fin 5 => (1 : ℝ)) 0 0
    simpa using h
  exact le_antisymm hle hge

/-! ## 卡目标 3：集合等式（固定名，两向证明） -/

/-- **卡目标 3（固定名 `growthValues_eq_normalized`）**：
`GrowthValues = NormalizedGrowthValues`。

* `⊆`：`A ≠ 0` + 合法轨迹 `values` + `g = growthRatio A values`。取 `A' := normalize A`：
  D08 给 `matrixEntryMax A' = 1`；D13 的 `legalTrace_normalize_iff` 把 `values` 的
  `(matrixEntryMax A)⁻¹` 缩放像变成 `A'` 的合法轨迹，而 `tracePeak_normalize` 给出
  该像的峰值恰为 `growthRatio A values = g`。不假定 `values` 唯一或路径存在。
* `⊇`：`matrixEntryMax A = 1` + 合法轨迹 + `g = tracePeak values`；由
  `ne_zero_of_matrixEntryMax_eq_one` 得 `A ≠ 0`，由
  `growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one` 得 `g = growthRatio A values`。 -/
theorem growthValues_eq_normalized : GrowthValues = NormalizedGrowthValues := by
  ext g
  constructor
  · rintro ⟨A, values, hA, htrace, rfl⟩
    refine ⟨Rho5.MatrixNormalization.normalize A,
      values.map (fun v => (matrixEntryMax A)⁻¹ * v), ?_, ?_, ?_⟩
    · exact Rho5.MatrixNormalization.matrixEntryMax_normalize A hA
    · exact (Rho5.CompletePivotPath.legalTrace_normalize_iff A hA values).mpr htrace
    · rw [tracePeak_normalize hA values]
      exact growthRatio_eq A values
  · rintro ⟨A, values, hmax, htrace, rfl⟩
    exact ⟨A, values, ne_zero_of_matrixEntryMax_eq_one hmax, htrace,
      (growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one hmax).symm⟩

/-- `growthValues_eq_normalized` 的成员形式：两个集合的成员谓词逐点等价
（`Set.ext_iff` 的直接读出，后继组装按成员使用）。 -/
theorem mem_growthValues_iff_mem_normalized {g : ℝ} :
    g ∈ GrowthValues ↔ g ∈ NormalizedGrowthValues := by
  rw [growthValues_eq_normalized]

/-- 反向的集合等式（两个方向都单独可引用）。 -/
theorem normalized_eq_growthValues : NormalizedGrowthValues = GrowthValues :=
  growthValues_eq_normalized.symm

/-! ## 卡目标 4：任意 `B` 下两个界命题的等价（后继全局最优证书消费） -/

/-- **卡目标 4（固定接口）**：对任意实数 `B`，
“所有非零矩阵的所有合法轨迹增长比 ≤ B” ⟺ “所有单位 entry-max 矩阵的所有合法轨迹
峰值 ≤ B”。

* `⇒`：任取 `matrixEntryMax A = 1` 的矩阵与合法轨迹，`A ≠ 0`，且该轨迹的增长比
  ≤ B；而单位 entry-max 下增长比就是峰值。
* `⇐`：任取非零矩阵 `A` 与其合法轨迹 `values`，取 `A' := normalize A`。D08 给
  `matrixEntryMax A' = 1`；D13 的整条轨迹缩放等价给出 `A'` 的合法轨迹
  `values.map (· * (matrixEntryMax A)⁻¹)`，其峰值 ≤ B；`tracePeak_normalize` 表明该峰值
  恰是 `growthRatio A values`。

因此后继 D18 只需给出归一化一侧的证书（D16 的盒界、D14 的路径存在都在那一侧使用），
无需在这条命题上再假设任何路径存在性或唯一性。 -/
theorem bound_iff_bound_normalized (B : ℝ) :
    (∀ (A : Matrix5) (values : List ℝ), A ≠ 0 →
        Rho5.CompletePivotPath.LegalTrace A values → growthRatio A values ≤ B) ↔
      (∀ (A : Matrix5) (values : List ℝ), matrixEntryMax A = 1 →
        Rho5.CompletePivotPath.LegalTrace A values → tracePeak values ≤ B) := by
  constructor
  · intro h A values hmax htrace
    have hb := h A values (ne_zero_of_matrixEntryMax_eq_one hmax) htrace
    rwa [growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one hmax] at hb
  · intro h A values hA htrace
    have hmax : matrixEntryMax (Rho5.MatrixNormalization.normalize A) = 1 :=
      Rho5.MatrixNormalization.matrixEntryMax_normalize A hA
    have htrace' : Rho5.CompletePivotPath.LegalTrace (Rho5.MatrixNormalization.normalize A)
        (values.map (fun v => (matrixEntryMax A)⁻¹ * v)) :=
      (Rho5.CompletePivotPath.legalTrace_normalize_iff A hA values).mpr htrace
    have hb := h (Rho5.MatrixNormalization.normalize A)
      (values.map (fun v => (matrixEntryMax A)⁻¹ * v)) hmax htrace'
    rwa [tracePeak_normalize hA values] at hb

/-- 卡目标 4 的集合形式：`B` 控制 `GrowthValues` 等价于 `B` 控制
`NormalizedGrowthValues`。由 `growthValues_eq_normalized` 与
`bound_iff_bound_normalized` 复合，供 D18 直接接入“全局最优证书”的界命题。 -/
theorem bound_growthValues_iff_bound_normalized (B : ℝ) :
    (∀ g ∈ GrowthValues, g ≤ B) ↔ (∀ g ∈ NormalizedGrowthValues, g ≤ B) := by
  rw [growthValues_eq_normalized]

end Rho5.GrowthModel
