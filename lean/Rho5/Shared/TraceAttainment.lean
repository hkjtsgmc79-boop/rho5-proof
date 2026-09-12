/-
D38 — 公开聚合入口：`import Rho5.Shared.TraceAttainment`
==========================================================

命名空间 `Rho5.TraceAttainment`。三层，逐层只依赖下一层：

* `Graph`        — **卡目标 A 的组合层**：定长补零轨迹图 `paddedGraph`、单步分支
  `paddedStepSet`（**所有**合法主元，含零主元，无额外非零前提）、按 D35 真实构造器的
  分支分解 `paddedGraph_succ`、`Fin.cons`/`List.ofFn` 拼装引理、连续 `Fin.cons`；
* `FiberCompact` — **卡目标 A**：纤维形式 `isCompact_paddedFiber`（对任意紧 `C` 与
  `ContinuousOn φ C`，沿 `φ` 的补零轨迹图紧；归纳覆盖每个主元分支，用 D32 的
  `CPDomain` 闭性与 Schur 连续性）与原形式 `isCompact_paddedGraph`；
* `PeakCompact`  — **卡目标 B**：`tracePeak (List.ofFn v)` 连续、紧域补零峰值集合紧
  `isCompact_paddedPeakSet`、与原 `LegalTrace` 峰值集合相等
  `legalPeakSet_eq_paddedPeakSet`、原路径峰值集合紧 `isCompact_legalPeakSet`。

* `GrowthAttainment` — **卡目标 C**：首主元域上原 `LegalTrace` 的峰值集合 = D17 真实
  `GrowthValues`（`peakSet_eq_growthValues`，经 D23 集合等式与 D26 桥）、真实增长值集合紧
  `isCompact_growthValues`、`rho5Trace` 是集合成员 `rho5Trace_mem_growthValues`，
  以及存在真实非零 `Matrix5` 与原 `LegalTrace` 达到 `rho5Trace`
  （`exists_nonzero_growthRatio_eq_rho5Trace`；`rho5Trace = sSup GrowthValues` 取自 D18）。

复用（只读冻结输入）：D35 `PaddedTrace`（关系与桥）、D32 `PivotSchurContinuity`
（`CPDomain`、闭性、含零点的 Schur 连续性）、D26 `FirstPivotCompact.Domain`
（矩阵乘积拓扑实例，**引用不重复声明**；本卡只额外桥接 `T2Space`，见 `FiberCompact`）
与 `FirstPivotCompact.Bridge`（D23 域桥 + 紧域）、D23 `FirstPivotDomain`（增长值集合
等式）、D18 `GrowthSupremum`（`rho5Trace`、非空）、D10 `pivotSchur`、
D17 `tracePeak`/`growthRatio`。

范围（冻结）：不定义第二套上确界、范数、主元谓词或轨迹关系；不假设任何非零性、有界性、
轨迹存在性或增长泛函连续性；不声称 rho5 最优或 `rho5Trace = alpha`；不构造外脑临界点
矩阵。卡目标 C 的达到性只由“集合紧 + 非空 + `sSup` 成员性”产生。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.TraceAttainment.Graph
import Rho5.Shared.TraceAttainment.FiberCompact
import Rho5.Shared.TraceAttainment.PeakCompact
import Rho5.Shared.TraceAttainment.GrowthAttainment
