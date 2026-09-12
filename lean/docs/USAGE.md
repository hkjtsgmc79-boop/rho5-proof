# 产品使用说明

默认只需 `import Rho5.PhaseOne`。该入口同时暴露33个便捷名称和原命名空间中的声明。下面示例基于 D161 已编译源码；其实际源码继续直接导入 C02 `Conditional`，没有为统一文档名称改写或重编。

示例文件有14个命名定理（12个主要结果和2个安全命题形状）、2个匿名 `example`；独立审计日志给出14项标准公理记录。新默认入口不会自动导入这些例子。

解析轨迹可调用 `Rho5.PhaseOne.exists_actual_trajectory`、`exists_physical_trajectory`、`exists_resource_endpoint`。它们保留起始 cube、严格时间空间预算，以及适用时的 Physical/资源前提；完整类型见 [公开类型](../FINAL_THEOREM_TYPES.txt)。

# USAGE — 第一阶段已验总装怎么用（D161）

适用对象：想在自己的 Lean 项目里**使用**已验的第一阶段总装结果的人。
本文件只描述**已经编译验证过**的入口与边界；完整类型与公理见 [完整公开类型](../FINAL_THEOREM_TYPES.txt) 与 [覆盖清单](COVERAGE.md)。示例源码：`../Rho5/PhaseOne/Examples.lean`（模块 `Rho5.PhaseOne.Examples`）。

先记住一句话：**本阶段交付的是"条件 sharp 终点 + 全部已付来源桥"，不是无条件的 `rho5Trace = α`。**

---

## 1. 一段 import、零参数即可用（无条件已证）

```lean
import Rho5.PhaseOne
open Rho5
```

| 想拿到的结论 | 直接调用 | 需要提供的证明参数 |
|---|---|---|
| `α` 是 `rootPolynomial` 在 `(4,5)` 中的唯一根 | `Rho5.Algebraic.AlphaRoot.exists_unique_root` | **无** |
| `4 < α < 5` 且 `rootPolynomial α = 0` | `alpha_gt_four`、`alpha_lt_five`、`alpha_is_root` | **无** |
| 上确界语义 `rho5Trace = sSup GrowthValues` | `Rho5.Shared.GlobalAttainedWitness.rho5Trace_semantics` | **无** |
| 实际达到：`matrixEntryMax actualAlphaMatrix = 1`、原 `LegalTrace`、`growthRatio = α` | `Rho5.ExternalAttainment.actualAlpha_attainment` | **无** |
| `α ≤ rho5Trace ≤ 81/16`（粗上界，**不是** sharp 上界） | `alpha_le_rho5Trace`、`rho5Trace_le_eighty_one_sixteenth` | **无** |
| `4 < rho5Trace` | `four_lt_rho5Trace` | **无** |
| 原全局最大者存在（真实矩阵 + 原合法路径 + 同高 + 全员支配） | `Rho5.Integration.StagedAssembly.baseline` | **无** |

这些结论**不需要任何数学假设**；Lean 的标准逻辑公理仍按原具名回执披露
（本卡审计实测：`{propext, Classical.choice, Quot.sound}`，无 `sorryAx`）。

## 2. 需要两个全域安全证明参数（未付）

```lean
open Rho5.Integration.StagedAssembly            -- XGlobalSafety
open Rho5.Shared.BRootCapacityEndpoint          -- RootEndpointSafety
```

| 想拿到的结论 | 定理 | 需要的参数 |
|---|---|---|
| `rho5Trace = α` | `rho5Trace_eq_alpha_of_safety` | `hX : XGlobalSafety`、`hB : RootEndpointSafety` |
| 任意非零原矩阵 + 原 `LegalTrace`：`growthRatio ≤ α` | `legal_growth_le_alpha_of_safety` | `hX`、`hB`（外加该矩阵/路径） |
| 同一路径第五读数 `values.getD 4 0 ≤ α * matrixEntryMax A` | `fifth_readout_le_alpha_of_safety` | `hX`、`hB` |
| 增长 > 4 时的第五读数识别 + 上界 | `high_path_fifth_of_safety` | `hX`、`hB`、`4 < growthRatio` |
| 行列式端点 `|det M| ≤ α * C M` | `det_endpoint_of_safety` | `hX`、`hB`、`M 0 0 = 1`、`PolyCP M` |

两个参数的确切形状（**这就是尚未完成的部分**）：

```lean
XGlobalSafety : Prop :=
  ∀ x : Rho5.LocalAnalysis.X, Rho5.LocalAnalysis.V43.Physical x →
    Rho5.LocalAnalysis.height x ≤ Rho5.Algebraic.AlphaRoot.alpha

RootEndpointSafety : Prop :=
  ∀ zStar : Rho5.Certificate.B16.Point,
    Rho5.Shared.BRootCapacityEndpoint.IsRootCapacityEndpoint zStar → zStar 23 ≤ alpha
```

* `XGlobalSafety` 是**完整** `Physical X` 域（不是某个 cube、某张 chart、某个有限样本）。
* `RootEndpointSafety` 覆盖所有 `IsRootCapacityEndpoint zStar`——即 `NormalizedB y` +
  `B17Root (frameOf y)` + `zStar = canonicalPoint (frameOf y)` 的原 D142 定义。
* 两者都必须提供**真实证明**：`axiom`、`sorry`、一个 `Bool`、Python 的 `PASS`、
  "有限样本无反例"、逐叶占位前提**都不能**充当它们。

## 3. 外部计算不会自动变成 Lean 证明

已经付清的是：来源桥（原全局最大者→实际 X 或 B、B→原完整根与同高容量端点、
Physical X→原矩阵/合法路径、原候选→实际 α）、上确界达到性、原前四 pivot 与第五归约。
**尚未**接入默认产品入口、也**不能**由外部计算结果替代的，是完整检查域/根覆盖的
来源与语义接线，以及由此产生的两项全域安全：

* 海量树/逐叶覆盖证书、C13–D157 等计算任务的 `PASS`、日志、有限样本检查
  → 它们可以作为**阶段二**的输入/清单，但**不会**自动给出 `hX` 或 `hB`；
  需要把覆盖责任形式化接成上表两个 `Prop` 的证明。
* 局部结论（某个 chart、某个小 k、某个前沿、某个 `x`）**不是**全域结论；
  使用时不要把局部实例的类型弱化后当作 `hX`/`hB`。
* 本阶段默认入口**不导入**任何具体树实例或后期检查器（实测边界检查见
  `RELEASE_READY.json` 的 `import_boundary`：C02 记录的 495 个源节点中
  Tree/Checker/Census/Subtree/V31/Mainline/CertificateContraction/G01–G03/C10/C12/Sample 命中数为 0）。

## 4. 直接可运行的示例

`../Rho5/PhaseOne/Examples.lean` 里有 12 个真实 `theorem/example`：
第 1 节全部零参数；第 2 节展示如何把 `hX`/`hB` 传进上表；第 3 节给出两个安全义务的原始形状。
编译方式见 `BUILDING.md`。**该文件不含任何无条件版本的 `rho5Trace = α`**，
也不含 `axiom`/`sorry`/`admit`/`native_decide`。

## 5. 常见误用

| 误用 | 事实 |
|---|---|
| 断言"本阶段已证 `rho5Trace = α`" | 只有**条件**版本；`hX`/`hB` 未付 |
| 把 `81/16` 当作 `α` 或当作 sharp 上界 | `α ≤ rho5Trace ≤ 81/16` 是**粗**上界 |
| 用某个树的 PASS 填入 `hX` | 类型不匹配，且会引入未付的覆盖接线 |
| 把 `Rho5.PhaseOne.Examples` 当成新数学 | 它只是既有定理的投影/调用示例 |
| 认为 X 上编译过就等于新机器能直接 build | 见 `BUILDING.md`：冷构建**未做** |
