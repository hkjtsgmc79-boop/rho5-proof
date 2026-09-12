# 外部计算及来源覆盖责任

本页复用 D159 已接收登记，不重跑其中引用的计算。两个完整全域责任仍是原 `XGlobalSafety` 与原 D142 `RootEndpointSafety`。本文提到的“原树未接收 / NOT_RECEIVED”只限定于所引冻结运行时 `IDENTITY.json` 的该次交接范围，不能据此断言整个项目从未持有原证书。所有阶段二样本只作索引，不是默认构建输入。

历史绝对路径只用于溯源；本包不包含那些计算运行时或证书载荷。原始登记与自审保留在 [D159证据](../evidence/D159/RELEASE_READY.json)。

# 第一阶段：外部计算责任与来源覆盖交接表（D159）

2026-09-12。本文件只做**外部计算依赖与可复现材料的对应登记**：把两个总责任（C02 原 `XGlobalSafety`、
原 D142 `RootEndpointSafety`）与现有计算模型/证书/验证器/回执逐项对上，并明确指出还欠什么。
本次只读既有回执、索引与有限入口源码；**未调用 Lean、未重跑任何外部计算、未展开压缩包全量、未扫描千万树**。
本文件不是新的证明回执，也不改变任何 owner 自审。

> **交付位置说明（重要）**：原卡指定交付到
> `outputs/phase1_noncomputational_assembly_20260912/D159/`，但本会话沙箱为 workspace-write，
> 对该目录的写入被拒绝（详见 `SELF_REVIEW.md` §交付位置的精确错误）。按“不得用替代路径绕过拒绝”的规则，
> 全部产物先落在本卡独占工作目录 `work/dsh-main/parallel/D159/`，**内容完整、可直接移动到上述交付目录**；
> 移动（或在授权后重写）需协调者/用户执行。

## 0. 两个总责任（原文 Prop，逐字取自源码）

```lean
-- C02 修订入口源码 outputs/relay_1345_delivery_20260912/C02/src/Rho5/Integration/StagedAssembly/Conditional.lean:16
def Rho5.Integration.StagedAssembly.XGlobalSafety : Prop :=
  ∀ x : LocalAnalysis.X, LocalAnalysis.V43.Physical x → LocalAnalysis.height x ≤ alpha

-- 原 D142 源码 work/dsh-main/parallel/D142/src/Rho5/Shared/BRootCapacityEndpoint/Refutation.lean:37
def Rho5.Shared.BRootCapacityEndpoint.RootEndpointSafety : Prop :=
  ∀ zStar : Point, Rho5.Shared.BRootCapacityEndpoint.IsRootCapacityEndpoint zStar →
    zStar 23 ≤ Rho5.Algebraic.AlphaRoot.alpha

-- 两者只作为公开前提被消费：
theorem Rho5.Integration.StagedAssembly.rho5Trace_eq_alpha_of_safety
    (hX : XGlobalSafety) (hB : RootEndpointSafety) : rho5Trace = alpha
```

**当前状态：`hX` 与 `hB` 都没有无条件证明。** 不能新增 `axiom hX`/`axiom hB`/`sorry`，也不能用
Python 的 `PASS`、一个 `Bool`、有限样本无反例、叶数或局部 PASS 填入它们。

## 1. 四类状态（本表每行落在其中之一，可并列）

| 代号 | 含义 |
|---|---|
| `REDUCTION_PROVEN` | 该步的**数学归约**已在 Lean 中证明（有正式接收回执与具名公理记录） |
| `COMPUTE_RECEIPT` | 该步存在**特定计算回执**（模型/证书/验证器与运行说明，路径+哈希可查） |
| `PAYLOAD_REPLAY` | 完整载荷/可移植重放是否已核验：`VERIFIED` / `UNKNOWN` / `NOT_RECEIVED` |
| `WIRING_OPEN` | 该步到**全域覆盖/语义接线**尚未形式化（保留精确 Prop 前提） |

## 2. 责任 OBL-X：`XGlobalSafety`（原 C02，X 侧）

总责任：**任意实际 X 状态（`V43.Physical x`）的高度不超过真实 `alpha`。**
所需形态 = 「所有相关原 X 源 → 完整检查域/根覆盖」的消费链 **加上** 该域上的完整叶/树计算证据。

| # | 逻辑责任 | Lean 类型 / 真实来源条件 | 模型/覆盖范围 | 已有计算材料与出处（路径 / 版本 / 哈希） | 现有回执证明了什么 | 还欠什么 | 状态 |
|---|---|---|---|---|---|---|---|
| X1 | **源→覆盖接线**：把「所有 `Physical x`」接到一个完整检查域 | `XGlobalSafety`（上文原文）；输入需 `Physical x`，无其它前提 | 全域 `LocalAnalysis.X` | 无独立计算材料；相关已付链条见 X2–X7；`outputs/phase1_noncomputational_assembly_20260912/ACCEPTED_CORE_MAP.md` §4「尚未完成的来源/语义接线」 | 已付：原全局最大者→实际 X 或 B（D131/D126）、Physical X→原矩阵/合法路径（D103_FULL）。**未付**：各局部图的起始区域、严格资格、时间/资源预算，以及所有实际相关源到完整检查域的消费链 | 全域源到覆盖的形式化消费链；一个局部门都不等于完整全域安全 | `WIRING_OPEN` |
| X2 | 有限线性证书规则的真实语义 | `Rho5.Shared.CertificateRules`；`results/CERTIFICATE_RULES_REAL_SOUNDNESS_READY.json` | 规则层（不含域覆盖） | `work/dsh-main/parallel/D135/results/{CERTIFICATE_RULES_REAL_SOUNDNESS_READY.json, CERTIFICATE_RULES_SCOPE_CORRECTION.json, CERTIFICATE_RULES_CORE_READY.json, CERTIFICATE_RULES_SAMPLES_READY.json}`；X `/root/microscope_ws/rho5_lean_dsh_20260911/D135/` | 未改动的精确 checker（`nonnegCheck`、`Rational.check`）配非负权重**排除坐标为实数**的全部赋值（不只是有理点）；两个新叶承载实值论证。**范围更正回执**明确：冻结 stage-A 语句原本只量词化有理点，此前文档措辞更宽 | 规则本身已付；**其应用到全域域覆盖**未付（属 X1/X6） | `REDUCTION_PROVEN` + `WIRING_OPEN` |
| X3 | 实际 X 源行与根盒 | `Rho5.Shared.XSmallKBranch.*`；106 条 `RowProp` + 22 维根盒 + 首 C 映射；`work/dsh-main/parallel/D136/results/X_V31_ACTUAL_MATRIX_106_ROWS_READY.json`、`X_V31_FIRST_C_SOURCE_READY.json` | 实际 `SatFrame` 类（带显式符号/正性/高值/小 k/`u₀` 前提） | X `/root/microscope_ws/rho5_lean_dsh_20260911/D136`（`build/lib/lean`）；`SourceSystem`/`chartState`/`boxLo·boxHi` | 106 行与根盒都是**结论**（非假设）；`sourceSystem_of_satFrame` 在显式前提下构造来源系统 | 其显式前提当时未消去；现由 D143（高值小 k 分支）消去，但**不是全域** | `REDUCTION_PROVEN`（分支级） |
| X4 | 实际矩阵→模型来源桥 + 实际原根 | `Rho5.Shared.XV31ModelEntry`；`matrix_has_v31_source_representative`、`matrixPoint_remaining_frontier`；`work/dsh-main/parallel/D148/results/X_SMALLK_ACTUAL_MATRIX_V31_MODEL_ENTRY_READY.json` | **仅**高值小 k 分支：`SatFrame M`、`qstar ≤ height M`、`k M ≤ 2` | X `/root/microscope_ws/rho5_lean_dsh_20260911/D148`；镜像 M01/M02/D135/D136/D143 对象 1995 个、0 冲突；M02_G01 冻结交付 27/27 逐字节一致 | 由**仅三个原前提**得到真实同高代表 `N`：`Model.SameSource (matrixPoint N)`、`matrixPoint N ∈ V31Prefix.root.denote`、且落在 M02 `FiveTree.remainingSeven` 的某个真实剩余盒 | 只覆盖高值小 k 分支；不覆盖任意 `Physical x`；剩余前沿未闭合 | `REDUCTION_PROVEN`（分支级） |
| X5 | 动态 cycle 波运行规则 | `Rho5.Shared.CertificateContraction.CycleRuntime*`；`runRecordBatches`、`runRecordBatches_preserves`、`runRecordBatches_empty`；`work/dsh-main/parallel/D153/results/DYNAMIC_CYCLE_WAVE_PROPAGATION_REAL_READY.json` | 运行规则层（每波动态行数、真实波序、C07/C03 后处理） | X `/root/microscope_ws/rho5_lean_dsh_20260911/D153`；冻结运行时 `dual_box.py d3963225…`、`pivot_windows.py e42100e5…`、`source_access.py 7c1160a3…` | 波表按真实顺序 `BASE→CHARTS→WINDOW→McCormick→本轮 cycle`、传播固定序无 cycle；动态 `m` 验证 `List RawRecord`；坏记录显式 error；同点保留与 EMPTY 消费者 | 是**运行规则实现**，不是全域覆盖；未对全域实例化任何真实 trace | `REDUCTION_PROVEN` + `WIRING_OPEN` |
| X6 | 树/叶实例（M01/M02/C10/C12/C09） | M01 `Rho5.Shared.MainlineTreeCover`（10 模块 / 65 具名公理检查，`PASS_FINITE_COVER_AND_ACTUAL_PREFIX_NOT_GLOBAL_CLOSURE`）；M02 `…V31Batch`（27 模块 / 408 具名公理目标）；C10 `…V31BatchKernel`；C12 | 具体子树/批次，非全域 | M01：`/Users/mike/Documents/Codex/2026-09-07/rho5-mainline-v2/work/lean_mainline_tree_cover_20260912/{READY.json, V31_FIRST_PREFIX_SAMPLE.json}`，输入哈希 `883ee574…`，X `/root/microscope_ws/mainline_v31_tree_cover_20260912`；M02：`outputs/relay_1408_delivery_20260912/M02_G01/{INTAKE_RECEIPT.json, BATCH_LEDGER.json, V31_BATCH_REAL_EMPTY_READY.json}`；C10：`work/codex-parallel/C10/{results/INTEGER_DATA_PROVENANCE.json, results/INDEPENDENT_KERNEL_REVIEW.md}`（根路径 `000001`、records 17–37、21 节点、scale 4800、raw_g02 `572eea3d…`）；C12：`work/codex-parallel/C12/{COMPUTE_FREEZE.json, results/DATA_PROVENANCE.json, results/GENERATOR_CONTROL_RESULTS.json}`；C09：`/Users/mike/Documents/Codex/2026-09-12/rho5-lean-staged-assembly/outputs/C09_actual_smallk_frontier/ACTUAL_SMALLK_FIVE_FRONTIERS_READY.json` | M01：**`full_V31_closed: false`**，保留 **8** 个前沿责任，`terminal_obligations_discharged_by_M01: 0`；M02_G01：pay 5 叶（records 10/11/14/15/16），`subtree_model_empty`，**剩余 7 前沿**，账本明写 `actual_matrix_to_polynomial_bridge: EXTERNAL_OBLIGATION`、`full_V31: OPEN`；C10：21 节点 G02 内核，独立源审「未发现 soundness 缺口」，但**不替代**成功编译回执与最终具名公理审计；C12：**FROZEN**，生成器对照自述 `EXTERNAL_ADAPTER_CONTROLS_PASSED_NOT_LEAN_PROOFS`；C09：高值小 k 分支关闭 3 条原路径、**剩 5 前沿** | 整棵 V31 与全域排除未闭合；C10/C12 属**冻结可选样本**；叶数、局部 PASS、Python 对照都不构成 `hX` | `COMPUTE_RECEIPT`（局部）+ `PAYLOAD_REPLAY: UNKNOWN` + `WIRING_OPEN` |
| X7 | 冻结运行时 = 证书/验证器参考语义 | 参考实现（非 Lean）：`dual_box.py::{rows_and_bounds, coefficients, bound_value, apply_wave, common_contract, replay_trace}`、`pivot_windows.py::{WINDOW_ROWS, PACKS, cycle_rows}`、`source_access.py` | 参考语义与格式 | X `/root/microscope_ws/rho5_deep500_all_open_20260910_08/runtime/deep500/v44/frozen/v41/`；`dual_box.py d3963225…`、`pivot_windows.py e42100e5…`、`source_access.py 7c1160a3…`、`discovery.py 91eede9b…`、`v41_protocol.py 55ee6ae8…`；`dependency/IDENTITY.json dbf81847…`（`received_zip_sha256 65e5bd5e…`、`reported_root_sha256 d350fc63…`、`b17_model_sha256 39a65f2c…`）；`dependency/RHO5_ROUND50_V40_LIGHT.zip 65e5bd5e…`（6520765 B） | 波序与传播序已由本阶段逐字核对：`rows_and_bounds` 39–63 行、`common_contract` 22 行为 `CHARTS→BASE→WINDOW`（无 cycle）。`IDENTITY.json` 自述 **`unreceived_original_tree_replayed_here: false`** —— **原树从未在此接收或重放** | Python 与 Lean 的**解析器/可执行等价**未形式化；原树载荷不可得 ⟹ 完整重放既未核验也无从核验（`待核对`：原树来源） | `COMPUTE_RECEIPT` + `PAYLOAD_REPLAY: NOT_RECEIVED` |

## 3. 责任 OBL-B：`RootEndpointSafety`（原 D142，B 侧）

总责任：**每个同框 canonical 根容量端点 `zStar` 的第 23 坐标不超过真实 `alpha`。**

| # | 逻辑责任 | Lean 类型 / 真实来源条件 | 模型/覆盖范围 | 已有计算材料与出处（路径 / 版本 / 哈希） | 现有回执证明了什么 | 还欠什么 | 状态 |
|---|---|---|---|---|---|---|---|
| B1 | 容量端点谓词与安全命题 | `IsRootCapacityEndpoint zStar := ∃ y, NormalizedB y ∧ B17Root (frameOf y) ∧ zStar = canonicalPoint (frameOf y)`；`RootEndpointSafety`（上文原文）；`work/dsh-main/parallel/D142/src/Rho5/Shared/BRootCapacityEndpoint/{Basic,Refutation}.lean` | 原完整 B17 根 | `work/dsh-main/parallel/D142/results/B_ROOT_CAPACITY_ENDPOINT_READY.json`；`outputs/assembly_intake_20260912/D142/INTAKE_RECEIPT.json`（4 源哈希、23 条 live binding、5 具名公理、`ACCEPTED_FOR_ASSEMBLY_WITH_EXPLICIT_PREMISES`） | 谓词与「同框 canonical 容量端点」构造已付；回执明写 **`RootEndpointSafety` 仍是显式未付前提**，无全域上界/`rho5Trace = alpha` 声称 | 安全命题本身 | `REDUCTION_PROVEN`（构造）+ 义务未付 |
| B2 | B17 根入口界 | `Rho5.Shared.PaperB17RootEntry.root_of_normalizedB_high`：`NormalizedB z → 0 ≤ z 14 → z 4 ≤ 0 → alpha < z 23 → B17Root (frameOf z)` | 「高」NormalizedB 分支 | `work/dsh-main/parallel/D134/results/{B17_ROOT_BOUNDS_READY.json, BUILD_STATUS.json}`（7 模块、7/7 exit 0、21 具名公理打印、非标准 0、staleness FRESH×7） | 从**真实重构**得到 17 条闭根界（不需要 D133）；符号代表由 D133 已接收门消费 | 这是**进入**根的充分条件（`alpha < z 23 ⟹` 在根内），取逆否才与安全相关；逆否/覆盖的全域量词仍未接 | `REDUCTION_PROVEN`（分支级） |
| B3 | 实际 ProperB → 根内代表 | `Rho5.Shared.ActualBRootEntry.Assembly.actual_properB_high_has_root_representative`；`work/dsh-main/parallel/D141/results/ACTUAL_PROPER_B_ROOT_READY.json`；`outputs/assembly_intake_20260912/D141/INTAKE_RECEIPT.json`（4 源哈希、8 条 live binding、11 具名公理） | 实际 `LeadingInput` + `ProperB` 且 `alpha < height` | X `/root/microscope_ws/rho5_lean_dsh_20260911/D141` | 实际 ProperB + `alpha < height` 给出**完整 B17 根内**的真实符号共轭 NormalizedB 代表，且保高 | 只覆盖「`alpha < height`」这一反证分支；无整根安全或全局等式 | `REDUCTION_PROVEN`（反证分支） |
| B4 | 同框 canonical 容量端点 | `Rho5.Shared.BRootCapacityEndpoint.root_capacity_endpoint`；C02 `exists_global_max_X_or_root_endpoint` | 原最大者 → N → 根容量端点 | 同 B1；C02 `results/FULL_TARGET_TYPES.txt` | 由原最大者经同高运输到达**原根**内的 canonical 容量端点（`y→zStar` 是同框构造，**不是**原矩阵的又一次符号共轭） | 该根上的**上界**未付（即 `hB` 本身） | `REDUCTION_PROVEN` |
| B5 | 高值收缩契约 | `C08_high_value_contract`：9 模块、123 公开声明、73 定理；`…/outputs/C08_high_value_contract.delivery.json`（`archive_sha256 b04e5ae2…`、`ready_sha256 e18d2527…`） | **仅** `high_value_contraction.contract` | `/Users/mike/Documents/Codex/2026-09-12/rho5-lean-certificate-contraction/outputs/C08_high_value_contract/`（+ `.tar.gz`） | 高值契约分支已编、归档清单已核 | 分支级；非整根覆盖 | `COMPUTE_RECEIPT` |
| B6 | base oracle 间隙 | `BASE_ORACLE_GAP_REAL_READY`；`…/C11_base_oracle_gap/results/{BASE_ORACLE_GAP_REAL_READY.json, BASE_ORACLE_RUNTIME_INPUTS.json, C11_ACTUAL_IMPORTS.json}`（97 交付文件、48 定理检查、4368 实际 import、`archive_sha256 787894d0…`） | 冻结 round48 `high_value_contraction.oracle_from_base(base, local_ports=False)`：default8 C08、有序 gap 重建/再交、实际 image/count/height、精确阈值态 | 同上；`source_predicate`：同一 `NormalizedB z`、`input aux.Contains z`、旧 gap 槽 22/23 含 z1−z2 与 z1−z3 | 同一 `z` 保留、`F(z) ≤ 精确阈值`；回执明写 **`inherited_EMPTY_qualification`：`CertifiedBase.ofEmpty` 需先有排除证明，不透明载荷本身不是证据** | 与 `IsRootCapacityEndpoint` 全域的**并轨**未做；oracle 参数域 ≠ 完整根 ⟹ `待核对` | `COMPUTE_RECEIPT` + `WIRING_OPEN` |
| B7 | 证书装配（提升轨迹源前沿） | `Rho5.Integration.CertificateAssembly`；`LIFTED_TRACE_SOURCE_FRONTIER_ASSEMBLY_READY`（`READY_SCOPED`） | 提升轨迹的**源前沿** | `/Users/mike/Documents/Codex/2026-09-12/rho5-lean-staged-assembly/outputs/C04_certificate_assembly/`；`canonical_base /root/microscope_ws/rho5_codex_c02_assembly_20260912/rebuild_01/build` | 提升轨迹源前沿装配已付（scoped） | 前沿之外未付；不等于整根 | `COMPUTE_RECEIPT`（scoped） |
| B8 | 实际小 k 五前沿（并行路线） | `Rho5.Integration.ActualSmallKFrontier.matrix_has_actual_five_frontier_representative`；`…/C09_actual_smallk_frontier/ACTUAL_SMALLK_FIVE_FRONTIERS_READY.json` | 高值小 k：`SatFrame M`、`qstar ≤ height M`、`k M ≤ 2` | 同上（`Audit`/`Entry`/`FirstLeaf` 源与 olean 哈希、成功日志哈希齐全，exit 0） | 关闭原路径 `0000000, 0000001, 000001`，**剩 5 前沿** `00001, 0001, 001, 01, 1`；同真实代表保 `SatFrame/height/k/r/w` | 与 D148 的 M02 剩余前沿列表对照可见额外关闭 2 条，但**没有任何回执把两条路线正式并轨** ⟹ `待核对`；5 前沿未闭合，且只覆盖小 k 分支 | `COMPUTE_RECEIPT` + `WIRING_OPEN` |

| B9 | 原 B16 deep11 源（两 chart 的波链） | `Rho5.Shared.B16Branch.{Defs,DefsAudit,Data,DataAudit,Qualification,…}`；`work/dsh-main/parallel/D140/results/{PHASE1_FROZEN.json, firstwave_paid_gate.json}` | 原 B16 深 11 记录 `10011101101`（两图 `B1\|N:L1-:L0+` / `B1\|N:L1-:L2+`，各 2 wave × 12 bounds） | `work/dsh-main/parallel/D140/results/`（模块源/olean 哈希与 `exit_code: 0` 逐条在 `PHASE1_FROZEN.json` 内，例如 `Defs` 源 `15933047…`/对象 `65facbfc…`）；`firstwave_paid_gate.json` 记 cycle 行已付、唯一剩余前提为 contracted box | 波链阶段在**自然边界**（已编译、已审计）冻结；第一波 cycle 行已付。冻结回执**显式列出「故意未做」**：curBox 包含实例（作为已证语句）、两 chart 的第二波、实际 two-chart 覆盖（coverage 前提）、两个 C 终端（D135 chart-1 50 行样本、D146 chart-2 51 行实例）的连接、以及完整 `B16_DEEP11_SOURCE_READY` 自审 | 上述五项全在第二阶段；**two-chart 覆盖前提不成立 ⟹ 不构成 B 侧全域安全** | `COMPUTE_RECEIPT`（第一波）+ `WIRING_OPEN` |

## 4. 交叉登记：冻结/可选与第二阶段

| 项 | 位置 | 本阶段处理 |
|---|---|---|
| C10 G02 批次内核 | `work/codex-parallel/C10/`；交付 `…/outputs/C10_g02_batch_kernel/` | **冻结可选样本**；不默认入口、不重跑 |
| C12 G03 批次规模 | `work/codex-parallel/C12/`；`COMPUTE_FREEZE.json`（`FROZEN`，2026-09-12T08:10:56Z） | 同上；生成器对照仅为外部适配器对照 |
| M01 前缀/有限覆盖 | X `/root/microscope_ws/mainline_v31_tree_cover_20260912` | 已接收；8 前沿保留 |
| M02 G01 五叶 | `outputs/relay_1408_delivery_20260912/M02_G01/` | 已接收（scoped）；7 前沿保留 |
| D140 B16 deep11 波链 | `work/dsh-main/parallel/D140/`；`results/PHASE1_FROZEN.json` | **自然边界冻结**；五项「故意未做」列于 B9 行 |
| C13 及 D154–D157、旧叶扩组 | 见 `work/dsh-main/tasks/DISPATCH_QUEUE.json` 策略字段（`PHASE1_NONCOMPUTATIONAL_LEAN_ASSEMBLY`） | **停在第二阶段**；本表只登记，不启动 |

## 5. 明确「待核对」（无证据的关联一律不写死）

1. **原树载荷**：`IDENTITY.json` 自述 `unreceived_original_tree_replayed_here: false`；原树既未接收也无重放回执
   ⟹ 「完整载荷/可移植重放已核验」对任何全域结论都**不成立**，本表记 `NOT_RECEIVED`；其确切来源与可否获得 = 待核对。
2. **C11 oracle 域 vs `IsRootCapacityEndpoint` 全域**：两者是否覆盖同一 `NormalizedB` 域，无回执说明 = 待核对。
3. **C09 与 M02 剩余前沿并轨**：两条路线的前沿列表可对照，但无正式并轨回执 = 待核对。
4. **冻结运行时与 Lean 语义的等价**：波序/传播序本阶段已逐字核对（X5/X7），但**解析器与可执行等价**未形式化 = 未形式化（不是已验证）。
5. **C06 runtime strict / C13**：本阶段未读其回执 = 待核对（不在此表下结论）。

## 6. 不得据此宣称的事

* 不得由 M01/M02/C10/C12/C09 的**叶数或局部 PASS** 宣称 `hX` 或 `hB`；
* 不得把 Python `PASS`、`check=true`、有限样本无反例当作全域证明；
* 不得把 `high_value_contract.contract`、`oracle_from_base`、小 k 分支、首 C 等**分支级**结论记成全域；
* 不得把 `y → zStar` 的同框 canonical 构造宣传成原矩阵的又一次符号共轭；
* 条件最终定理 `rho5Trace_eq_alpha_of_safety hX hB` 属第一阶段逻辑总装，**不等于**无条件 `rho5Trace = alpha` 已完成。
