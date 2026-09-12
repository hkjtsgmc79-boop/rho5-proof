/-
D32 — 公开聚合入口：`import Rho5.Shared.PivotSchurContinuity`
==============================================================

命名空间 `Rho5.PivotSchurContinuity`。四层，逐层只依赖下一层：

* `CPDomain`     — 合法主元域 `CPDomain p q = {A | IsCompletePivot A p q}`（任意 `n`），
  闭性、含零、零主元 ⇒ `A = 0`（D10）、条目连续性、`pivotSchur 0 p q = 0`、
  以及“条目盒子 ∩ 域”紧（**卡目标 1**、目标 4 的零件）；
* `Bound`        — **卡目标 2**：`|pivotSchur A p q i j| ≤ 2 * |A p q|`（含零主元；
  非零情形搬运 D11 的 `fixedSchur` 界经 D10 的实际重索引）；
* `Continuous`   — **卡目标 3**：显式公式处处相等、非零主元处连续除法、
  零点处用目标 2 的估计挤压、合起来 `ContinuousOn (pivotSchur · p q) (CPDomain p q)`；
* `CompactImage` — **卡目标 4**：紧域与盒子交域的 Schur 像紧，以及未付接口清单
  （全路径有限分支/零填充表示、峰值函数、后续步复合、`sSup`/`rho5` 达到）。

复用（只读冻结输入，哈希见 `INPUT_HASHES.json`）：D26 `FirstPivotCompact.Domain`
（实矩阵乘积拓扑实例 `instTopologicalSpaceMatrix`，本卡**不**重复声明、不改 `Matrix`
可约性）、D11 `PivotGrowth`（`fixedSchur_entry_abs_le_two_mul_pivot`，实现者自审已收存）、
D10 `PivotReindex`（`pivotSchur`、`pivotSchur_apply`、`movePivot` 及其主元/位置引理、
零主元 ⇒ 零矩阵）、pilot `IsCompletePivot`/`Matrix`。

范围（冻结）：**不**从“单步像紧”跳到 `rho5` 达到；**不**证峰值函数连续、**不**定义 `sSup`、
**不**复制 D26 的首步多项式连续性、**不**对不合法主元声称条目估计；不用 Mathlib 总入口。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.PivotSchurContinuity.CPDomain
import Rho5.Shared.PivotSchurContinuity.Bound
import Rho5.Shared.PivotSchurContinuity.Continuous
import Rho5.Shared.PivotSchurContinuity.CompactImage
