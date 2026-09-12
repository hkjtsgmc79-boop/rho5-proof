/-
D53 — 公开聚合入口：`import Rho5.Shared.TailSignNormalization`
================================================================

命名空间 `Rho5.TailSignNormalization`。三层，逐层只依赖下一层：

* `Signs`     — 末位行/列**符号数据**：阶 5/4/3/2 上「除最后一位为 `ε` 外全为 `1`」的符号向量、
  `IsSign` 资格、逐条目求值与逐阶尾限制恒等式（`sigma5` 的 `succ` 尾是 `sigma4`，等等）；
* `Transport` — 用 D22 真实 `pivotSchur_signedEntries`（显式非零前提 `M 0 0 ≠ 0`、`p M ≠ 0`、
  `k M ≠ 0`）逐阶运输：`S4 N = signedEntries (S4 M) (sigma4 ε) (sigma4 η)`（`S3`/`T2` 同理），
  于是 `p N = p M`、`k N = k M`、`r N = r M`、`s N = η * s M`、`t N = ε * t M`、
  `T2 N 1 1 = ε * η * (T2 M 1 1)`；
* `Normalize` — `δ N = ε * η * δ M`、`|δ N| = |δ M|`、四层 CP 保持、`matrixEntryMax`/`M 0 0 = 1`/
  原 `LegalTrace`/增长比保持，以及**选择** `ε = if 0 ≤ t M then 1 else -1`、
  `η = if 0 ≤ s M then 1 else -1`（零取 `+1`）得到 `0 ≤ s N`、`0 ≤ t N` 的真实整矩阵；
* `Witness`   — 接 D48 已验收的条件式见证（前提 `4 < rho5Trace`），给出非负尾符号版本的
  真实全局最大见证（增长比与原全局比较不变，末两步峰值二分保持）。

复用只读：D22 `signedEntries`/`LegalTrace` 符号运输、D37 真实 `S4/S3/T2/p/k/r/s/t`、
D41 符号核心（经 D48）、D48 `CanonicalTail`。**不**重证上游、**不**发明第二套符号语义、
**不**假设或声称 `d = -r`、满秩、全域平衡、`rho5 = alpha`。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.TailSignNormalization.Signs
import Rho5.Shared.TailSignNormalization.Transport
import Rho5.Shared.TailSignNormalization.Normalize
import Rho5.Shared.TailSignNormalization.Witness
