/-
D23 — 公开聚合入口：`import Rho5.Shared.FirstPivotDomain`
=========================================================

命名空间 `Rho5.FirstPivotDomain`。四层，逐层只依赖下一层：

* `Domain`      — 冻结集合 `FirstPivotGrowthValues`（`matrixEntryMax A = 1`、
  `A 0 0 = 1`、`IsCompletePivot A 0 0`、真实 `LegalTrace`，元素值为 D17 的原
  `growthRatio`）与“域 ⊆ 真实增长值”；
* `PivotEntry`  — 完整主元的绝对条目 = 冻结元素最大范数；非零矩阵的真实轨迹给出非零完整
  主元（D13）；D10 `movePivot` 与 D20 `permuteEntries` 的桥，以及搬主元下的元素最大范数与
  轨迹不变性（D20 固定引理，值列表原样保留）；
* `Reduce`      — **卡目标 2**：`exists_firstPivot_reduction` 把任意非零矩阵的真实轨迹约化到
  域中（搬主元 + 以主元倒数整体缩放，含原主元为负；轨迹整条按 `|·|` 缩放，增长比不变）；
* `SetEquality` — **卡目标 3/4**：固定名 `growthValues_eq_firstPivotGrowthValues`，以及任意实
  `B` 的三个界等价入口（集合形式、矩阵形式、两者之桥）。

复用（只读冻结输入，哈希见 `INPUT_HASHES.json`）：D17 `Rho5.Shared.GrowthModel`
（`GrowthValues`、`growthRatio`、`growthRatio_smul`、`growthRatio_eq`、
`ne_zero_of_matrixEntryMax_eq_one`）、D20 `Rho5.Shared.TracePermutation`
（`permuteEntries`、`legalTrace_permute_iff`、`matrixEntryMax_permuteEntries`）、
D10 `Rho5.Shared.PivotReindex`（`movePivot` 及其位置/主元/非零性引理）、
D13 `Rho5.Shared.CompletePivotPath`（`LegalTrace`、`exists_step_of_ne_zero`、
`legalTrace_smul`）、D08 `MatrixNormalization`（元素最大范数基本事实与 `smul` 缩放）、
pilot `Rho5.Matrix5`/`matrixEntryMax`/`IsCompletePivot`。本聚合不导入
`Rho5.Shared.FirstPivotDomain.Audit`（审计模块只被构建脚本单独编译）。

范围（冻结）：**不**定义 `sSup`、**不**声称集合非空或有界、**不**证明 alpha 最优或达到性、
**不**假设未知矩阵参数化、**不**导入 D18/D22 活动草稿、**不**重新定义增长比/范数/主元谓词。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.FirstPivotDomain.Domain
import Rho5.Shared.FirstPivotDomain.PivotEntry
import Rho5.Shared.FirstPivotDomain.Reduce
import Rho5.Shared.FirstPivotDomain.SetEquality
