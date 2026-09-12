/-
D35 — 公开聚合入口：`import Rho5.Shared.PaddedTrace`
====================================================

命名空间 `Rho5.PaddedTrace`。四层，逐层只依赖下一层：

* `Basic`    — **卡目标 1/2**：定长零填充关系 `PaddedLegalTrace`（任意合法主元都可递归，
  无额外非零前提）、长度恰为阶数、零矩阵轨迹恰为 `List.replicate n 0`（存在且唯一）；
* `Bridge`   — **卡目标 3**：与原 `Rho5.CompletePivotPath.LegalTrace` 的固定双向桥
  `paddedLegalTrace_iff`（补零 = `values ++ List.replicate (n - values.length) 0`），
  按真实构造器 `empty`/`zeroStop`/`step` 分情形，且不假定原路径满长；
* `Peak`     — **卡目标 4**：补零保持 `tracePeak`，`List.ofFn` 向量峰值集合与原合法路径
  峰值集合相等，`growthRatio`/`GrowthValues` 只经相同分母搬运、定义未改；
* `Examples` — `n = 0`、零 `1×1`、非零 `1×1` 的编译例子（末端不多加 `0`）。

复用（只读冻结输入）：D10 `pivotSchur` 及其条目公式与“零主元⇒零矩阵”、
D13 `LegalTrace`（`length_le`、三个真实构造器）、D17 `tracePeak`/`growthRatio`/`GrowthValues`。
本卡不重定义原路径语义，不引入拓扑/紧性内容（那属于后继 D38）。

范围（冻结）：**不**声称任何路径存在性来自矩阵本身（桥只在给定轨迹之间搬运）、
**不**做紧性或达到性、**不**定义 `sSup`、**不**触碰 D26/D32 的实例与连续性。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.PaddedTrace.Basic
import Rho5.Shared.PaddedTrace.Bridge
import Rho5.Shared.PaddedTrace.Peak
import Rho5.Shared.PaddedTrace.Examples
