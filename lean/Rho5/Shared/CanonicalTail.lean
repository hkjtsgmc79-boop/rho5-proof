/-
D48 — 公开聚合入口：`import Rho5.Shared.CanonicalTail`
========================================================

命名空间 `Rho5.CanonicalTail`。四个可独立自审的层：

* `Defs`       — 卡上记号 `δ = d - t * s / r`（`d = T2 A 1 1`）与它的真实 `pivotSchur`
  身份，以及末位 `1 × 1` 块的统一读数（覆盖 `lastStep`/`step`/`zeroStop`，不假设末主元非零）；
* `Prefix`     — **目标 1**：`matrixEntryMax M = 1`、`M 0 0 = 1`、`LeadingTracePos M values`、
  `4 < growthRatio M values` 时，`M`、`S4 M`、`S3 M`、`T2 M` 的 `(0,0)` 都是真实完整主元，
  `p M`、`k M`、`r M` 严格为正，且 `values.length = 5`；
* `TailValues` — **目标 2**：`values = [1, p M, k M, r M, |δ M|]`，增长比 = 峰值，峰值落在
  第四项（`r M`）或第五项（`|δ M|`），对应 `4 < r M` 或 `4 < |δ M|`；末值允许为 `0`；
* `Envelope`   — **目标 3**：D46 的实际尾块包络 `growthRatio M values ≤ r M + |s M * t M| / r M`；
* `Witness`    — **目标 4**：以 `4 < rho5Trace` 为**假设**，用 D43 的无前提存在定理给出带全部
  上述资格与尾部公式、并保留原全局比较的真实规范见证。

状态模型全部复用 D37 已验收的同名 Schur 定义；达到性复用 D43；符号核心复用 D41（经 D43）；
包络复用 D46。不重证上游、不假设尾块平衡/满秩/B24 覆盖/`rho5Trace = alpha`。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.CanonicalTail.Defs
import Rho5.Shared.CanonicalTail.Prefix
import Rho5.Shared.CanonicalTail.TailValues
import Rho5.Shared.CanonicalTail.Envelope
import Rho5.Shared.CanonicalTail.Witness
