/-
D17 — 公开聚合入口：`import Rho5.Shared.GrowthModel` 得到整条增长比/归一化接口。
================================================================================

命名空间 `Rho5.GrowthModel`。四层，逐层只依赖下一层：

* `TracePeak` — 冻结定义 `tracePeak (values) := values.foldr max 0`（全阶段最大值，
  不是最后一项）与其非负性、成员上界、`0 ≤ B` 下峰值 ≤ `B`、非负标量齐次性；
* `Scalar`    — 冻结定义 `growthRatio A values = tracePeak values / matrixEntryMax A`、
  `GrowthValues` 的比值语义、合法非零轨迹 `growthRatio ≥ 1`、非零标量（含负）不变性、
  峰值界到比值界的接口；
* `Unit`      — D08 单位归一化后的峰值与增长比等式（轨迹不缩放与轨迹缩放两种写法）；
* `NormalizeSet` — 冻结集合 `GrowthValues`、`NormalizedGrowthValues`，固定名
  `growthValues_eq_normalized`，以及任意 `B` 下两个界命题的等价
  `bound_iff_bound_normalized`。

复用（只读冻结输入，哈希见 `INPUT_HASHES.json`）：`Rho5.Shared.Conventions`、
`Rho5.Shared.Pivot`（pilot）、`Rho5.Shared.MatrixNormalization`（D08）、
`Rho5.Shared.PivotReindex*`（D10）、`Rho5.Shared.CompletePivotPath*`（D13）。
本聚合不导入 `Rho5.Shared.GrowthModel.Audit`（审计模块只被构建脚本单独编译）。

范围（冻结）：**不**定义最终 `rho5` 的上确界，**不**声称 `GrowthValues` 非空或有界，
**不**证明候选矩阵达到性，**不**证明 `sSup` 或 alpha 最优性，**不**重复 D14 路径存在、
D15 粗界 16、D16 盒证书或外脑 G04 临界点存在。不重复实现任何冻结语义
（`matrixEntryMax`、`IsCompletePivot`、`normalize`、`LegalTrace` 均原样复用）。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.GrowthModel.TracePeak
import Rho5.Shared.GrowthModel.Scalar
import Rho5.Shared.GrowthModel.Unit
import Rho5.Shared.GrowthModel.NormalizeSet
