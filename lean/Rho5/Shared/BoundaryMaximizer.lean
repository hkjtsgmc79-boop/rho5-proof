/-
D68 — `Rho5.Shared.BoundaryMaximizer` 聚合入口
================================================

阶段 A 的对外入口（子模块**不** import 本聚合，避免环）：

* `Rho5.Shared.BoundaryMaximizer.Core`
  — 具名事实包 `BoundaryMaximizerCore` / `SortedBoundaryMaximizerFacts`、
    转置不变性 `BoundaryMaximizerCore.transpose`、桥接引理 `traceValues_shift_eq`；
* `Rho5.Shared.BoundaryMaximizer.Sorted`
  — 实际存在性 `exists_sorted_boundary_maximizer`（D57 四边界最大者 + D63 整矩阵转置排序）
    与紧凑形式 `exists_sorted_boundary_maximizer_four_faces`。

审计在同目录的 `Rho5/Shared/BoundaryMaximizer/Audit.lean`（只由构建链最后编译）。
-/
import Rho5.Shared.BoundaryMaximizer.Core
import Rho5.Shared.BoundaryMaximizer.Sorted
import Rho5.Shared.BoundaryMaximizer.Balanced
