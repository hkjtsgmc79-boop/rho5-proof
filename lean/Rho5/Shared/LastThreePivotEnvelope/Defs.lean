/-
D87 阶段 A — 实际最后三阶包络：定义层
=====================================

卡片 `parallel/D87/TASK.md` 阶段 A 的构造部分。对**实际**五阶 `M`（`M 0 0 = 1`，
`PolyCP M`）取出**已经存在**的第三个 Schur 更新 `S3 M`（D37 的 `Rho5.Certificate.
B24Extraction.S3`），并用它的首主元 `k M = S3 M 0 0 > 0` 归一化：

  `scaledS3 M = (k M)⁻¹ • S3 M`

这个 `3 × 3` 矩阵就是 D83 外脑包络定理 `fixed_order_three_pivot_envelope` 的**实际输入**
（三次多项式情形的真实归一化三阶块），而不是任何抽象盒松弛。

**本层不做什么**（卡上的边界）：

* 不重新推导 D83 的数学包络——`Rho5.ExternalThreePivot` 的具名定理按哈希绑定的 olean
  只读复用；
* 不假设尾部增长（没有 `r ≤ 4`、没有 `T2 1 1 = -r` 之外的隐藏前提）；
* 不要求五个主元全部非零；`delta M` 的符号任意（`0`/负/正都覆盖，见 `StageA`）；
* 不声称 `rho ≤ alpha`，也不声称 `rho ≤ 81/16`——那是阶段 B。

阶段 A 只付清"实际 `S3/k` 就是 D83 包络的合法输入，且它的两个读数恰是 `r/k` 与
`|delta|/k`"这一段。
-/
import Rho5.Shared.MinorCPDomain.Poly
import Rho5.Shared.CanonicalTail.Defs
import Rho5.ExternalThreePivot.MatrixEnvelope

namespace Rho5.LastThreePivotEnvelope

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S3 T2 p k r s t)

/-- **A3 —— 实际最后三阶块的归一化**：第二个 Schur 更新 `S3 M` 除以它自己的首主元 `k M`。
定义只用 D37 已验收的实际 `S3`/`k`，没有新的矩阵模型。 -/
noncomputable def scaledS3 (M : Matrix5) : Matrix (Fin 3) (Fin 3) ℝ :=
  (k M)⁻¹ • S3 M

end Rho5.LastThreePivotEnvelope
