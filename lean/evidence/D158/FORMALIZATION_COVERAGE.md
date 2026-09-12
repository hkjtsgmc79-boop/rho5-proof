# D158 — FORMALIZATION_COVERAGE / 已验成果正式覆盖清单（第一阶段非大规模计算总装）

状态：只读清点转写，**本次未调用 Lean、未重审数学、未重跑证书、未复制全库**。
输入：`ACCEPTED_CORE_MAP.md`、`PACKAGING_BOUNDARY.md`（同目录）及其引用的已接收回执。
语言：中英文兼容（中文说明 + 英文模块名/定理名/路径）。凡未核实者一律写 **未知/未付**，不以外部 PASS、Bool 或有限样本充当全域证明。

对应目录（本卡交付）：`outputs/phase1_noncomputational_assembly_20260912/D158/`（本地产出目录见 `RELEASE_READY.json` 的 `produced_at`）。

---

## 0. 一页结论 / One-page summary

| 项 | 现状 | 类别 |
|---|---|---|
| 实际 `alpha` 的根身份（存在、隔离区间、唯一） | 已无条件证明 | A |
| 原候选系统与 `alpha` 接通；原候选/临界点在候选盒中的存在唯一性 | 已无条件证明 | A |
| 实际矩阵达到 `alpha`；`alpha ≤ rho5Trace` | 已无条件证明 | A |
| 原上确界语义、粗界 `rho5Trace ≤ 81/16`、原全局最大者存在 | 已无条件证明 | A |
| 任意原矩阵/路径前四 pivot 与第五归约 | 已无条件证明（第五→cap 需第五读数上界，见 B） | A/B |
| Physical X ↔ 实际矩阵/原合法路径（保留一般 `w`） | 已无条件证明 | A |
| 原全局最大者 → 实际 X 或 B（保留 P/values/N/同高） | 已无条件证明 | A |
| B 原来源 → 原 B17 根容量端点（`IsRootCapacityEndpoint`） | 已无条件证明；容量端点根上界未付 | A/C |
| 条件 sharp 等式与原终点（`rho5Trace_eq_alpha_of_safety` 等） | **保留 hX/hB 参数** | B |
| 真实解析轨迹（D84 `PhysicalTrip`：ODE 存在、资源终点、guard） | **保留 cube/预算前提** | B |
| `XGlobalSafety` 与 `RootEndpointSafety` 的无条件证明 | **未付** | C |
| 局部图/覆盖资格、起始区域、时间资源预算的全域接线 | **未付** | C |
| 海量树/内核证书、后期收紧检查器实例 | 延后（第二阶段） | D |

**不能读出**：本清单不构成无条件 `rho5Trace = alpha`，不构成 whole X 安全、不构成 `alpha` 安全目标已完成的声明。

---

## 1. A 类：已无条件证明 / Unconditionally proved

> 判据：该定理没有待提供的数学假设（Lean 标准逻辑公理按原具名回执披露：`propext`、`Classical.choice`、`Quot.sound`）。

### A1. 实际 `alpha` 的真实根身份 — Actual alpha root identity
* 模块/命名空间：`Rho5.Algebraic.AlphaRoot.Root` / `Rho5.Algebraic.AlphaRoot`
* 公开名：`exists_root_in_exact_interval`、`alpha_in_exact_interval`、`alpha_is_root`、`exists_unique_root`、`root_unique`、`alpha_gt_four`、`alpha_lt_five`
* 内容：在精确隔离区间内存在实根；`alpha` 由已证存在选择，在 `(4,5)` 中唯一。
* 未含：**无** `RootSpec`、外部存在性或唯一性假设。
* 接收：D09 独立回执 `evidence/D09_COORDINATOR_RECEIPT.json`；当前 C02 闭包再次实际消费。
* 备注：D09 早期回执里“临界点存在未做”一类历史备注已被 D34/D30/D82 后续交付覆盖，**不得再列为当前欠账**。

### A2. 原候选方程与实际 `alpha` 接通 — Candidate system ↔ actual alpha
* 模块：`Rho5.Algebraic.ScalarCandidateAlpha`（`candidate_system_eq_actual_alpha`）；`Rho5.Algebraic.CriticalExistence.Compatibility`/`.ActualAlpha`（`exists_unique_original_system`、`criticalPoint_g_eq_alpha`、`exists_critical_at_actual_alpha`）
* 内容：D34 给候选盒加原 `P1=P2=P3=J=0` 推出 `g = alpha`；G04/D30 证明原系统在候选盒中的存在唯一性、以及实际 `alpha` 临界元组存在。
* 未含：候选存在已不再是外部输入。
* 接收：`evidence/D34_INTAKE_RECEIPT.json`、`evidence/D30_ORIGINAL_READY.json`、`evidence/D30_ALPHA_READY.json`。

### A3. 实际矩阵达到 `alpha` — Attainment
* 模块/命名空间：`Rho5.ExternalAttainment.ActualAlpha` / `Rho5.ExternalAttainment`
* 公开名：`actualAlpha_attainment`、`exists_actualAlpha_attainment`、`actualAlpha_le_rho5Trace`
* 内容：`actualAlphaMatrix` 元素最大值 = 1、原 `LegalTrace` 成立、实际增长等于真实 `alpha`，且属于增长值集合，故 `alpha ≤ rho5Trace`。
* 未含：无候选存在、CP 或元素界外部前提。
* 接收：`evidence/D82_INTAKE_RECEIPT.json`（`ACCEPTED_DECLARED_SCOPE`）。

### A4. 原上确界语义、粗界、原全局最大者存在 — Supremum, coarse bound, global maximizer
* 模块：`Rho5.Shared.GlobalAttainedWitness.Range` / `.Attained`；命名空间 `Rho5.Shared.GlobalAttainedWitness`
* 公开名：`rho5Trace_semantics`、`alpha_le_rho5Trace`、`rho5Trace_le_eighty_one_sixteenth`、`four_lt_rho5Trace`、`global_max_exists`
* 内容：`rho5Trace = sSup GrowthValues`；`alpha ≤ rho5Trace ≤ 81/16`；存在原实际矩阵/合法路径的全局最大者。
* 边界：`81/16` 是**粗上界，不是 sharp α 上界**；上确界达到性不再欠缺。
* 接收：`evidence/D92_GLOBAL_RANGE_READY.json`、`evidence/D92_GLOBAL_ATTAINED_READY.json`、C02 回执。

### A5. 原任意路径前四 pivot 与第五归约 — First four pivots and fifth reduction
* 模块：`Rho5.ExternalFourthPivot.SharpEarly` / `.FifthReduction`；命名空间 `Rho5.ExternalFourthPivot`
* 公开名：`early_pivot_bounds_including_zero`、`growth_above_four_is_fifth`、`growth_le_of_fifth_readout_le`
* 内容：任意原矩阵与原 `LegalTrace` 的前四读数满足 `1, 2, 9/4, 4` 倍元素最大值，覆盖零、短路径、并列 pivot；原增长 > 4 时第五原读数即峰值且路径长 5。
* 边界：`growth_le_of_fifth_readout_le` 需要**该第五读数的上界**作为输入（C02 由两项安全命题提供），因此“第五→任意 cap”属 B 类，不属无条件。
* 接收：`evidence/D124_INTAKE_RECEIPT.json`；`evidence/D86_INTAKE_RECEIPT.json` 为其已验上游（完整第四 pivot）。

### A6. Physical X 与原实际矩阵/路径对应 — Physical X ↔ actual matrix / legal trace
* 模块：`Rho5.Shared.V43ActualMatrix.Trace` / `.Frame`；命名空间 `Rho5.Shared.V43ActualMatrix`
* 公开名：`legalTrace_M`、`growthRatio_ge_height`、`height_le_rho5Trace`、`polyCP_M`
* 内容：任意 `V43.Physical x` 构造真实归一化矩阵 `M x`，真实轨迹读数 `[1, pOf x, kOf x, rOf x, |wOf x − rOf x|]`，实际增长至少 height，故 `height ≤ rho5Trace`。
* 边界：保留一般 `w`；无额外 `LeadingTracePos` 输入；**该方向不给出 `height ≤ alpha`**。
* 接收：`evidence/D103_INTAKE_RECEIPT.json`（`ACCEPTED_A_AND_B_FULL_SCOPE`）；已含在 C02 最终绑定。

### A7. 原全局最大者 → 实际 X / B（保留来源） — Global maximizer → X or B
* 模块：`Rho5.Shared.GlobalXBMaximizer.Basic` / `.StageB`；下层 `Rho5.Shared.ActualXBReduction.CanonicalXB`
* 公开名：`exists_global_ts_maximizer`、`exists_global_max_X_or_properB`
* 内容：无外部最大者存在假设；保留实际原最大者 `P`、合法路径、实际 tail 代表 `N` 与同高关系；`X` 是重构回 `N` 的 Physical 点，`B` 是实际 `ProperB`。
* 边界：**未**声称 `B` 已进入最终全树安全域。
* 接收：`evidence/D131_INTAKE_RECEIPT.json`、`evidence/D126_INTAKE_RECEIPT.json`。

### A8. B 原来源 → 原 B17 根容量端点 — B source → root capacity endpoint
* 模块：`Rho5.Shared.ActualBRootEntry.Assembly`（`actual_properB_high_has_root_representative`）；`Rho5.Shared.BRootCapacityEndpoint.Basic`（`root_capacity_endpoint`）；C02 `exists_global_max_X_or_root_endpoint` / `exists_X_or_root_endpoint`
* 内容：C02 用显式反证分支 `alpha < rho5Trace` 接通 原最大者 → `N` → 实际符号代表 → 同框 canonical 容量端点；`LeadingInput N` 与同高运输由既有 TailReduction 支付。
* 边界：容量端点属于**完整原根**；该根的上界（`RootEndpointSafety`）**未付**。符号变换止于 `N→z→y`；`y→zStar` 是同框 canonical 容量构造，**不得**宣传为原矩阵的又一次符号共轭。
* 接收：`evidence/D141_INTAKE_RECEIPT.json`、`evidence/D142_INTAKE_RECEIPT.json`、`evidence/D139_INTAKE_RECEIPT.json`、C02 回执。

---

## 2. B 类：保留参数的证明 / Proofs retaining explicit parameters

> 判据：结论已证，但公开类型中保留明确的数学前提；这些前提目前**没有**无条件证明，且不得用 `axiom`/`sorry`/Bool/样本填入。

### B1. 条件 sharp 等式与原终点 — Conditional assembly endpoint（C02 默认主线）
* 模块：`Rho5.Integration.StagedAssembly.Conditional`（传递导入 `RootReduction → Baseline`）；命名空间 `Rho5.Integration.StagedAssembly`
* 公开名与保留前提：
  * `rho5Trace_eq_alpha_of_safety (hX : XGlobalSafety) (hB : RootEndpointSafety) : rho5Trace = alpha`
  * `legal_growth_le_alpha_of_safety`（同 `hX`/`hB`；任意 `A : Matrix5`、`values : List ℝ`、`A ≠ 0`、原 `CompletePivotPath.LegalTrace A values` ⇒ `growthRatio A values ≤ alpha`）
  * `legal_growth_le_alpha_via_fifth_of_safety`、`fifth_readout_le_alpha_of_safety`、`high_path_fifth_of_safety`
  * `det_endpoint_of_safety`：`∀ M, M 0 0 = 1 → MinorCPDomain.PolyCP M → |M.det| ≤ alpha * MinorGrowthThreshold.C M`
* 另外两项已证的上下界与最大者：`baseline`（无条件，属 A 类组合接口）；`exists_global_max_X_or_root_endpoint`、`exists_X_or_root_endpoint`（强归约，保留 `alpha < rho5Trace` 反证分支与原来源）。
* 完整公开类型：`evidence/C02_FULL_TARGET_TYPES.txt`（编译器实际输出，本卡不重新 print 全库）。
* 接收：`evidence/C02_INTAKE_RECEIPT.json`（`ACCEPTED_SCOPED`，三门接收）、`evidence/C02_ASSEMBLY_*_READY.json`。
* 纪律：可新增 `axiom hX`、`axiom hB`、`sorry` 一律禁止；条件定理**不得**改名成无条件结果。

### B2. 真实解析轨迹 — D84 `PhysicalTrip`（本阶段有限新增）
* 模块/命名空间：`Rho5.ExternalV43Existence.Trajectory` / `.PhysicalTrip` / `Rho5.ExternalV43Existence`
* 公开名与保留前提（对 `z0 : X`、时间 `T`、起始半径 `d`）：
  * `exists_actual_trajectory`：需 `0 ≤ T`、`z0 ∈ cube center d`、`d + (9/4)*T < radius`；输出 `γ 0 = z0` 与闭时间区间上的真实 `HasDerivAt γ (certifiedField (γ t)) t`。
  * `exists_physical_trajectory`：再需 `Physical z0`、`T ≤ consumed z0`；同一 `γ` 满足留在 cube、位移 ≤ `(9/4)t`、高度至少增加 `t/16`、held guard 不变、released guard 至少增加 `(2/5)t`、资源按 `consumed z0 − t` 下降、坐标 7 不变、`Physical` 保持。
  * `exists_resource_endpoint`：取 `T = consumed z0` 得真实终点资源为零且 Physical；`exists_exhaustion_at_own_resource` 为自身资源时间的公开特化。
  * `exists_guard_boundary_trajectory`：guard 边界轨迹存在。
  * `height_le_of_actual_trip`：**仍显式输入**局部 cube 上的 height 上界及补偿损失/时间关系；不能用它凭空支付 `XGlobalSafety`。
* 边界：ODE 轨迹存在是结论而非前提；尚未把每个相关全局源放进该局部图并支付预算；**不自证局部或全域 alpha 上界**，不得伪称已接完全域排除。
* 接收：`evidence/D84_INTAKE_RECEIPT.json`（`ACCEPTED_DECLARED_SCOPE`）。本阶段作为“有限新增”并入默认主线。

### B3. 可选（**不进入默认闭包**）— Optional, not in the default closure
* `Rho5.Shared.V43PositiveResourceEscape`（命名空间 `Rho5.V43PositiveResourceEscape`）：`exists_escape_with_small_displacement`、`not_isLocalHeightMaxOnPhysical`、`consumed_eq_zero_of_isLocalHeightMaxOnPhysical`；保留局部图/内部资格，不是全 X 覆盖。接收：`evidence/D100_INTAKE_RECEIPT.json`。
* `Rho5.Shared.V43CompactBoundary`（命名空间 `Rho5.V43CompactBoundary`）：`isCompact_K`、`exists_height_maxOn`、`maximizer_boundary_or_exhausted`；仍需其 `K` 的源成员/非空资格。接收：`evidence/D108_INTAKE_RECEIPT.json`。
* 两者**可以登记复用**，但不得为使第一阶段“收齐模块”而自动引入整个后期检查器目录，更不得反过来弱化两项安全命题。

---

## 3. C 类：尚未形式化的来源连接 / Source-and-coverage wiring not yet formalized

> 判据：结论尚未在 Lean 中建立；此处给出**精确 Prop 前提**与覆盖清单，禁止用启动大量叶实例代替定义范围。

### C1. 完整 `XGlobalSafety` — 未付
```lean
Rho5.Integration.StagedAssembly.XGlobalSafety : Prop :=
  ∀ x : Rho5.LocalAnalysis.X,
    Rho5.LocalAnalysis.V43.Physical x →
    Rho5.LocalAnalysis.height x ≤ Rho5.Algebraic.AlphaRoot.alpha
```
* 现状：**没有**无条件证明。已付的是 A6（`height ≤ rho5Trace`）与 A4（`alpha ≤ rho5Trace`），两者方向都不足以给出 `height ≤ alpha`。
* 归属：原始计算证书/树覆盖的溯源责任由 **D159** 承担（全域安全 ID `XGlobalSafety` 与 D159 交叉引用）；D158 只登记接口与来源边界。

### C2. 原 D142 `RootEndpointSafety` — 未付
```lean
Rho5.Shared.BRootCapacityEndpoint.IsRootCapacityEndpoint zStar :=
  ∃ y, Rho5.ExternalBFibreCapacity.NormalizedB y ∧
    Rho5.Shared.PaperB17RootEntry.B17Root (Rho5.ExternalBFibreCapacity.frameOf y) ∧
    zStar = Rho5.ExternalBFibreCapacity.canonicalPoint (Rho5.ExternalBFibreCapacity.frameOf y)

Rho5.Shared.BRootCapacityEndpoint.RootEndpointSafety : Prop :=
  ∀ zStar : Rho5.Certificate.B16.Point,
    Rho5.Shared.BRootCapacityEndpoint.IsRootCapacityEndpoint zStar →
    zStar 23 ≤ Rho5.Algebraic.AlphaRoot.alpha
```
* 现状：**没有**无条件证明；不得替换为抽象 `completeX/completeB` 布尔标记、单个局部叶或有限样本。
* 归属：同 C1，与 **D159** 交叉引用（同一 ID 不重复登记计算证书溯源）。

### C3. 局部图资格、起始区域、时间/资源预算的全域接线 — 未付
* 各局部图的起始区域与严格资格（cube、内部性、`LeadingTracePos` 一类结构前提）；
* D84 轨迹的严格时间/空间预算：`0 ≤ T`、`z0 ∈ cube center d`、`d + (9/4)T < radius`、`T ≤ consumed z0`；
* 所有实际相关源 → 完整检查域/根覆盖的消费链（含 `BASE106`、动态传播、有限收缩结论各自的来源限定）；
* 部分局部来源已由后续门支付，但**没有一个局部门等于两项完整全域安全**。

### C4. 语义未决项（明确写未知）
* 尚未核验是否存在把“所有实际相关源”一次性接入完整检查域/根覆盖的现成组合定理；本清单**不**声称存在。
* 本卡未核验 C02 闭包以外的下游消费点；组装者若扩大默认 import，需自行重做边界检查。

---

## 4. D 类：延后的大规模计算 / Deferred large-scale computation

* 完整相关根/树及全域排除的内核证书与全部必要覆盖责任：**默认不导入具体树实例**；未来证明经原 `hX`/`hB` 接口接入。
* 已验但**默认不 import**：`G01/G02/G03` 数据入口、`M01/M02`、`C10`（树核/样本总装）、后续 `C13–D157` 收紧级联。C02 的 `DEPENDENCIES.json` 把 `D136_SOURCE_SYSTEM`、`M01`、`C01` 等登记为 `ACCEPTED_AVAILABLE_NOT_IMPORTED`。
* C02 修订图的实测：项目图中 `G01/G02/G03`、`V31/Mainline/Census/Subtree/Tree/Checker/Leaf`、`CertificateContraction` 名称匹配均为 **0**，实际加载的 Rho5 清单为 0；即可达节点数 Baseline **404** / RootReduction **492** / Conditional **495**（原公共聚合模块另加 1，共 **496** 个项目加载模块）。数字来自已有图，不是新的逐模块源码审计。
* 第二阶段可登记复用、但本阶段不得引入：新 `BASE106`、动态传播、有限收缩结论（各有来源限定）；原 X 大于某阈值、小 `k` 或某一前沿的结论**不能**记成全域。
* “非大规模计算”**不**要求删除已有解析证明的有限精确数据：实际 α/G04 的隔离、候选、Bézout、Jet/Center 等有限证书是当前达到性的真实依赖，保留其已有证明，无需重新生成或冷编。已有 `LocalAnalysis` 有限 chart 常量不因此升格为全域覆盖。

---

## 5. 真实解析轨迹的定位 / Where the real analytic trace sits

| 层 | 内容 | 类别 |
|---|---|---|
| 原矩阵/路径读出 | A6 `legalTrace_M`、`growthRatio_ge_height`、`height_le_rho5Trace` | A |
| 前四 pivot/第五归约 | A5 `early_pivot_bounds_including_zero`、`growth_above_four_is_fifth` | A |
| 第五读数 → cap | `growth_le_of_fifth_readout_le`（需第五上界，由 hX/hB 提供） | B |
| 轨迹存在 | B2 `exists_actual_trajectory`、`exists_physical_trajectory` | B |
| 资源终点 | B2 `exists_resource_endpoint`、`exists_exhaustion_at_own_resource` | B |
| 全域上界 | `XGlobalSafety`、`RootEndpointSafety` | C（D159 交叉引用） |

---

## 6. 边界与禁止事项 / Boundaries and prohibitions

1. 本清单**不**声称无条件 `rho5Trace = alpha`，**不**声称 whole X 安全或 `alpha` 安全目标完成。
2. 新增 `sorry`/`admit`/项目公理/`native_decide` 一律禁止；不得以 Python `PASS`、一个 Bool、有限样本无反例、逐叶占位前提填入 `hX`/`hB`。
3. 两项安全命题可在 README/coverage 中标为阶段二外部计算责任接口，但必须说明其证明还包含正式的来源/覆盖接线。
4. `RootSpec`、根存在、候选临界点存在**已消除**，不得重新列为欠账；D09/D34 早期回执中的历史备注以本清单为准。
5. 不重复 D159 的计算证书溯源；全域安全 ID 与 D159 交叉引用。不复制全源码（D160 负责源码包），不写使用示例（D161 负责）。
6. 未核验事实写“未知”，不给出无依据的全项目完成百分比。

---

## 7. 交付物索引 / Deliverable index

| 文件 | 内容 |
|---|---|
| `FORMALIZATION_COVERAGE.md` | 本文件：四类覆盖清单 |
| `THEOREM_CATALOG.json` | 逐项稳定 ID、模块、真实公开名、前提/结论、接收回执、类型出处、是否默认入口 |
| `ACCEPTED_EVIDENCE_INDEX.md` | 可迁移相对路径需求 ↔ 现有回执映射 |
| `RELEASE_READY.json` | 本卡交付回执（含实际产出路径与哈希） |
| `SELF_REVIEW.md` | 本次新增核验 vs 复用证据、抽查记录、未核验项 |
| `SHA256SUMS` | 本目录全部产物哈希 |
| `evidence/` | 少量核心原回执与完整公开类型（编译器实际输出）副本 |
