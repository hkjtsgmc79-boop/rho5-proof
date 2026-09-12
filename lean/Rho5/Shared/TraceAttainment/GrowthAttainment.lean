/-
D38 — **卡目标 C**：真实增长值集合的紧性与 `rho5Trace` 的真实达到
=================================================================

本文件把 A/B 的紧性结果接到 D17/D18/D23/D26 的**真实**增长值世界，四步：

* `peakSet_eq_growthValues`（C1，集合等式）——首主元域 `K` 上**原** `LegalTrace` 的峰值集合
  **等于** D17 的真实增长值集合 `Rho5.GrowthModel.GrowthValues`：
  `⊆` 用 D26 的桥 `mem_firstPivotGrowthValues_iff_exists_mem_firstPivotDomain` 加 D17 的
  `growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one`（`K` 的成员都有 `matrixEntryMax = 1`）；
  `⊇` 用 D23 的冻结集合等式 `growthValues_eq_firstPivotGrowthValues` 的成员展开。
  两向都只做拆装，不新增假设。
* `isCompact_growthValues`（C2，紧性）——B 的 `isCompact_legalPeakSet` 取
  `C = firstPivotDomain`（D26 `isCompact_firstPivotDomain`），再用 C1 换回
  `GrowthValues`。**没有**对增长泛函另加连续性假设：紧性来自 A/B 的补零轨迹图链。
* `rho5Trace_mem_growthValues`（C3，`sSup` 成员性）——`rho5Trace = sSup GrowthValues`
  （D18 的 `rho5Trace_eq`）落在 `GrowthValues` 内，由 C2 的紧性与 D18 的
  `growthValues_nonempty` 用 `IsCompact.sSup_mem` 得到。
* `exists_tracePeak_eq_rho5Trace` / `exists_nonzero_growthRatio_eq_rho5Trace`
  （C4/C5，**卡目标 C 的存在命题**）——存在**真实** `Matrix5` `A ≠ 0` 与**真实**合法轨迹
  `values`，使 `growthRatio A values = rho5Trace`；这是 C3 的成员展开，不构造外脑临界点矩阵。

只读复用（不重编）：A/B 的 `PeakCompact`（`isCompact_legalPeakSet`）、D26
`FirstPivotCompact.Bridge`（桥 + `isCompact_firstPivotDomain`，经 `Schur ↦ Compact ↦ Domain`）、
D23 `FirstPivotDomain`（`growthValues_eq_firstPivotGrowthValues`）、D17 `GrowthModel`
（`growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one`）、D18 `GrowthSupremum`
（`rho5Trace`、`rho5Trace_eq`、`growthValues_nonempty`）。

范围（冻结）：不定义第二套上确界/范数/主元谓词或第二套轨迹关系，不假设任何非零性、有界性、
轨迹存在性或增长泛函连续性，不声称 `rho5Trace = alpha`、不声称 rho5 最优，不构造外脑临界点
矩阵。`A ≠ 0` 与 `LegalTrace A values` 都是结论里的**合取项**，不是隐藏前提。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.TraceAttainment.PeakCompact
import Rho5.Shared.FirstPivotCompact.Bridge
import Rho5.Shared.GrowthSupremum

namespace Rho5.TraceAttainment

open Rho5

/-- **C1（集合等式）**：`K` 上原 `LegalTrace` 的峰值集合 = D17 的真实 `GrowthValues`。

两向都真证明：`⊆` 把 `K` 成员的 `matrixEntryMax = 1` 经 D17 的
`growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one` 变成 `growthRatio`，再用 D26 桥的 `mpr`；
`⊇` 先经 D23 的集合等式落到 `FirstPivotGrowthValues`，再拆出 `K` 成员并反过来用同一个
`growthRatio = tracePeak` 引理。 -/
theorem peakSet_eq_growthValues :
    {p : ℝ | ∃ A ∈ Rho5.FirstPivotCompact.firstPivotDomain, ∃ values : List ℝ,
        Rho5.CompletePivotPath.LegalTrace A values ∧ p = Rho5.GrowthModel.tracePeak values}
      = Rho5.GrowthModel.GrowthValues := by
  rw [Rho5.FirstPivotDomain.growthValues_eq_firstPivotGrowthValues]
  ext p
  constructor
  · rintro ⟨A, hA, values, htrace, rfl⟩
    obtain ⟨hmax, h00, hpiv⟩ := hA
    refine (Rho5.FirstPivotCompact.mem_firstPivotGrowthValues_iff_exists_mem_firstPivotDomain).mpr
      ⟨A, ⟨hmax, h00, hpiv⟩, values, htrace, ?_⟩
    exact (Rho5.GrowthModel.growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one hmax).symm
  · rintro ⟨A, values, hmax, h00, hpiv, htrace, hp⟩
    exact ⟨A, ⟨hmax, h00, hpiv⟩, values, htrace,
      hp.trans (Rho5.GrowthModel.growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one hmax)⟩

/-- **C2（紧性）**：真实增长值集合 `GrowthValues` 紧。

由 B 的 `isCompact_legalPeakSet` 作用于 D26 的紧域 `firstPivotDomain`，再经 C1 换回
`GrowthValues`；不对增长泛函加任何连续性假设。 -/
theorem isCompact_growthValues : IsCompact (Rho5.GrowthModel.GrowthValues : Set ℝ) := by
  rw [← peakSet_eq_growthValues]
  exact isCompact_legalPeakSet Rho5.FirstPivotCompact.isCompact_firstPivotDomain

/-- **C3（`sSup` 成员性）**：`rho5Trace` 本身属于 `GrowthValues`。

`rho5Trace` 是 `GrowthValues` 的上确界（D18 的 `rho5Trace_eq`，`rfl` 级）；紧集非空，故
上确界是集合成员（`IsCompact.sSup_mem`），非空性用 D18 的 `growthValues_nonempty`
（其见证是最初的 all-ones 矩阵的真实轨迹）。 -/
theorem rho5Trace_mem_growthValues :
    Rho5.GrowthSupremum.rho5Trace ∈ Rho5.GrowthModel.GrowthValues := by
  rw [Rho5.GrowthSupremum.rho5Trace_eq]
  exact IsCompact.sSup_mem isCompact_growthValues Rho5.GrowthSupremum.growthValues_nonempty

/-- **C4（达到性的峰值形式）**：存在 `K` 中矩阵与真实合法轨迹，其**峰值**等于 `rho5Trace`。 -/
theorem exists_tracePeak_eq_rho5Trace :
    ∃ A ∈ Rho5.FirstPivotCompact.firstPivotDomain, ∃ values : List ℝ,
      Rho5.CompletePivotPath.LegalTrace A values ∧
        Rho5.GrowthModel.tracePeak values = Rho5.GrowthSupremum.rho5Trace := by
  have h : Rho5.GrowthSupremum.rho5Trace ∈
      {p : ℝ | ∃ A ∈ Rho5.FirstPivotCompact.firstPivotDomain, ∃ values : List ℝ,
        Rho5.CompletePivotPath.LegalTrace A values ∧ p = Rho5.GrowthModel.tracePeak values} := by
    rw [peakSet_eq_growthValues]
    exact rho5Trace_mem_growthValues
  obtain ⟨A, hA, values, htrace, hpeak⟩ := h
  exact ⟨A, hA, values, htrace, hpeak.symm⟩

/-- **C5（卡目标 C 的存在命题）**：存在**真实非零** `Matrix5` 与**真实**原 `LegalTrace`，
其增长比 `growthRatio` 恰等于 `rho5Trace`。

这是 `rho5Trace_mem_growthValues` 的成员展开：`A ≠ 0`、`LegalTrace A values` 与
`growthRatio A values = rho5Trace` 都是结论的合取项。 -/
theorem exists_nonzero_growthRatio_eq_rho5Trace :
    ∃ A : Matrix5, A ≠ 0 ∧ ∃ values : List ℝ,
      Rho5.CompletePivotPath.LegalTrace A values ∧
        Rho5.GrowthModel.growthRatio A values = Rho5.GrowthSupremum.rho5Trace := by
  obtain ⟨A, values, hA, htrace, hratio⟩ := rho5Trace_mem_growthValues
  exact ⟨A, hA, values, htrace, hratio.symm⟩

end Rho5.TraceAttainment
