/-
D90 — `Rho5.Shared.LastPivotUpperReduction` 聚合入口
====================================================

用实际第四主元界消去全局尖锐上界的一半义务（原 D17 卡 D90）。子模块**不** import 本
聚合（避免环）；审计在同目录的 `Audit.lean`，只由构建链最后编译。

* `…/Common` — 公共支付步 `C M ≤ T * B M`（消费 D86 实际 `r M ≤ 4`）；
* `…/StageA` — 目标 A：`PolyCP` 全域单一实际行列式界 iff，及端点 `T := rho5Trace`
  处的无条件推论 `det_bound_rho`；
* `…/StageB` — 目标 B：D74 排序四面边界域上的同一 iff（四面全保留）；
* `…/StageC` — 目标 C：`T := alpha`（D09）的精确终点形式（全域版 + 排序版）；
* `…/StageD` — 目标 D：`4 < rho5Trace` 时同一 D68 排序四面最大者的真实
  `|δ P| = rho5Trace`。

所有上游（D86 D68 D69 D74 D67 D44 D09）都是**只读复用**：X 侧构建树按逐字节哈希核对后
硬链接，不重编、不修改。本 lane 不声称 `rho5Trace ≤ alpha`、不声称
`4 < rho5Trace`、不声称满秩/平衡/最大值可达，也不改进 `rho` 本身的数值界。
-/
import Rho5.Shared.LastPivotUpperReduction.Common
import Rho5.Shared.LastPivotUpperReduction.StageA
import Rho5.Shared.LastPivotUpperReduction.StageB
import Rho5.Shared.LastPivotUpperReduction.StageC
import Rho5.Shared.LastPivotUpperReduction.StageD
