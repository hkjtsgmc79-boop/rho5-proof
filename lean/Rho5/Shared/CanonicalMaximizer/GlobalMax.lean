/-
D43 — 阶段 A（1）：`rho5Trace` 是真实增长值集合的全局最大元素
================================================================

把已验收的 D38 C 阶段达到性与 D18 的上确界上界组装成**全局比较接口**：`rho5Trace`
既属于 D17 的真实集合 `Rho5.GrowthModel.GrowthValues`（D38 的
`rho5Trace_mem_growthValues`），又是它的上界（D18 的 `le_rho5Trace`），因此存在一对
**真实**的非零 `Matrix5` 与原 `LegalTrace`，其增长比等于 `rho5Trace`，并且对每个真实
非零矩阵与每条原 `LegalTrace` 都给出上界。

这里**不重新证明**紧性或达到性（D38 已付），也不把「全局比较」当作前提：比较是这两条
冻结结论的直接推论；反向地，`eq_rho5Trace_of_forall_le` 说明任何「支配所有真实矩阵/
路径」的见证其增长比**必然**等于 `rho5Trace`（这是结论，不是最大化器证书里的假设）。

只读复用（不重编）：D38 `Rho5.Shared.TraceAttainment`（成员性）、D18
`Rho5.Shared.GrowthSupremum`（`le_rho5Trace`、`rho5Trace_eq`）。

范围（冻结）：不假设 `rho5Trace = alpha`、不假设尾块平衡/满秩/B24 覆盖，不构造具体数值
矩阵；不新增紧性、非零性或存在性前提。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.TraceAttainment
import Rho5.Shared.GrowthSupremum

namespace Rho5.CanonicalMaximizer

open Rho5

/-- **A1（矩阵形式，全局比较）**：任意真实非零 `Matrix5` 的任意原 `LegalTrace`，其 D17
增长比不超过 `rho5Trace`。这是 D18 上界引理对 `GrowthValues` 成员的直接应用：见证矩阵、
值列表、非零性与轨迹关系全部由输入提供，**没有**任何新前提。 -/
theorem growthRatio_le_rho5Trace {N : Matrix5} (hN : N ≠ 0) {ws : List ℝ}
    (htrace : Rho5.CompletePivotPath.LegalTrace N ws) :
    Rho5.GrowthModel.growthRatio N ws ≤ Rho5.GrowthSupremum.rho5Trace :=
  Rho5.GrowthSupremum.le_rho5Trace ⟨N, ws, hN, htrace, rfl⟩

/-- **A1（集合形式）**：`rho5Trace` 是 `GrowthValues` 的上界（D18 的冻结引理原样复用）。 -/
theorem le_rho5Trace_of_mem_growthValues {g : ℝ}
    (hg : g ∈ Rho5.GrowthModel.GrowthValues) : g ≤ Rho5.GrowthSupremum.rho5Trace :=
  Rho5.GrowthSupremum.le_rho5Trace hg

/-- **A1（最大元素，展开形式）**：成员性（D38 阶段 C）+ 上界性（D18）。按卡要求直接给出
这一对，不引入任何中间证书结构。 -/
theorem rho5Trace_mem_and_le :
    Rho5.GrowthSupremum.rho5Trace ∈ Rho5.GrowthModel.GrowthValues ∧
      ∀ g ∈ Rho5.GrowthModel.GrowthValues, g ≤ Rho5.GrowthSupremum.rho5Trace :=
  ⟨Rho5.TraceAttainment.rho5Trace_mem_growthValues,
    fun _ hg => Rho5.GrowthSupremum.le_rho5Trace hg⟩

/-- **A1（全局最大见证）**：存在真实非零 `Matrix5` `M` 与原 `LegalTrace` `values`，使
`growthRatio M values = rho5Trace`，且**对每个**真实非零 `N` 与**每条**原 `LegalTrace`
`ws` 有 `growthRatio N ws ≤ growthRatio M values`。

`M`、`values`、`LegalTrace`、`M ≠ 0` 与等式都是结论的合取项；全局比较由 A1 的矩阵形式
在等式上改写得到，不是假设。 -/
theorem exists_globalMaximizer :
    ∃ M : Matrix5, M ≠ 0 ∧ ∃ values : List ℝ,
      Rho5.CompletePivotPath.LegalTrace M values ∧
        Rho5.GrowthModel.growthRatio M values = Rho5.GrowthSupremum.rho5Trace ∧
          ∀ (N : Matrix5), N ≠ 0 → ∀ ws : List ℝ,
            Rho5.CompletePivotPath.LegalTrace N ws →
              Rho5.GrowthModel.growthRatio N ws ≤ Rho5.GrowthModel.growthRatio M values := by
  obtain ⟨M, values, hM, htrace, hratio⟩ := Rho5.TraceAttainment.rho5Trace_mem_growthValues
  refine ⟨M, hM, values, htrace, hratio.symm, ?_⟩
  intro N hN ws hws
  rw [← hratio]
  exact growthRatio_le_rho5Trace hN hws

/-- **A1（支配者必然取到上确界）**：若某个真实非零矩阵与真实轨迹的增长比支配**所有**
真实矩阵/路径的增长比，则该增长比恰为 `rho5Trace`。这条把「最大化器证书」变成可检验的
结论（而不是被假设的东西）：上界方向用 A1，反向用 D38 的达到性对 `N := M` 取到
`rho5Trace`。 -/
theorem eq_rho5Trace_of_forall_le {M : Matrix5} (hM : M ≠ 0) {values : List ℝ}
    (htrace : Rho5.CompletePivotPath.LegalTrace M values)
    (hmax : ∀ (N : Matrix5), N ≠ 0 → ∀ ws : List ℝ,
      Rho5.CompletePivotPath.LegalTrace N ws →
        Rho5.GrowthModel.growthRatio N ws ≤ Rho5.GrowthModel.growthRatio M values) :
    Rho5.GrowthModel.growthRatio M values = Rho5.GrowthSupremum.rho5Trace := by
  obtain ⟨M', hM', values', htrace', hratio'⟩ :=
    Rho5.TraceAttainment.exists_nonzero_growthRatio_eq_rho5Trace
  refine le_antisymm (growthRatio_le_rho5Trace hM htrace) ?_
  rw [← hratio']
  exact hmax M' hM' values' htrace'

end Rho5.CanonicalMaximizer
