/-
D43 — 公开聚合入口：`import Rho5.Shared.CanonicalMaximizer`
============================================================

命名空间 `Rho5.CanonicalMaximizer`。**阶段 A 与阶段 B 都已交付**：

* `GlobalMax` — 全局比较层：`rho5Trace` 是真实集合 `Rho5.GrowthModel.GrowthValues`
  的成员（D38 阶段 C）与上界（D18），因此任意真实非零矩阵的任意原 `LegalTrace` 增长比
  `≤ rho5Trace`（`growthRatio_le_rho5Trace`）；存在**真实**全局最大见证
  （`exists_globalMaximizer`）：非零 `Matrix5` + 原 `LegalTrace` + 增长比等于 `rho5Trace`
  + 对所有真实矩阵/路径的上界；反向地，任何支配所有见证的增长比必然等于 `rho5Trace`
  （`eq_rho5Trace_of_forall_le`）。
* `LeadingRepresentative` — 规范化首位置代表：用 D38 的实际首主元域峰值见证经 D40 的
  **一次静态行列置换**得到条目最大值 `1`、带 `LeadingLegalTrace`、增长比等于 `rho5Trace`
  且带同一全局比较的真实 `Matrix5`（`exists_leading_normalized_maximizer`、
  `exists_normalized_leading_maximizer`、`exists_leading_normalized_maximizer_full`）；
  并给出首位置主元**非零**（`leading_corner_ne_zero`，**不**等于 `+1`）、值列表首项
  `= |M 0 0|`（`exists_cons_of_leading`）与长度 `≤ 5`（`leading_length_le_five`）。

* `CanonicalRepresentative` — **阶段 B**：消费 D41 已证符号核心（`LEADING_SIGNS_CORE_READY.json`
  门：`LeadingTracePos`、`leadingLegalTrace_of_leadingTracePos`、`exists_signs_leadingTracePos`）
  与 D22 的符号不变性（`matrixEntryMax_signedEntries5`、`growthRatio_signedEntries5`），把阶段 A
  的条目最大值 `1` 首位置最大矩阵升级为：静态行符号 `s` 下 `B = signedEntries5 A s 1` 满足
  `matrixEntryMax B = 1`、`B ≠ 0`、**`B 0 0 = 1`**、`LeadingTracePos B values`（**正前缀**，
  最后 `1 × 1` 主元不强转正、早停零主元不声称正）、`LeadingLegalTrace B values`、
  `values.length ≤ 5`、`growthRatio B values = rho5Trace = tracePeak values` 与同一全局比较
  （`exists_canonical_representative`、`exists_canonical_maximizer`）。

范围（冻结）：不重证紧性、达到性或 D41/D22 的符号核心（都不重编）；不假设
`rho5Trace = alpha`、不假设尾块平衡/rank 2/B24 盒覆盖/满秩、不构造外脑临界点矩阵、
不声称最后 `1 × 1` 主元为正或五个非零主元。所有存在性结论的合取项都是结论。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.CanonicalMaximizer.GlobalMax
import Rho5.Shared.CanonicalMaximizer.LeadingRepresentative
import Rho5.Shared.CanonicalMaximizer.CanonicalRepresentative
