# D159 可复现性索引：外部计算材料 / 证书 / 验证器 / 运行说明

2026-09-12。本索引登记两个总责任（`XGlobalSafety`、`RootEndpointSafety`）所依赖的**现有**计算材料与回执，
给出路径、版本与哈希出处，并逐项标注「可复现到什么程度」。**本次未运行其中任何一项。**

## 0. 固定环境（复用已验事实，不改动）

| 项 | 固定值 | 出处 |
|---|---|---|
| Lean | `4.30.0`，X `x86_64-unknown-linux-gnu`，commit `d024af099ca4bf2c86f649261ebf59565dc8c622` | `PACKAGING_BOUNDARY.md` §4 |
| mathlib | `c5ea00351c28e24afc9f0f84379aa41082b1188f` | 同上 |
| lake manifest SHA256 | `6fa600a652ca1ef77814e08127d1078febb38e3018ed9f8b1c5683b92427b789` | 同上 |
| 规范 C02 对象根 | `/root/microscope_ws/rho5_codex_c02_assembly_20260912/rebuild_01/build` | `ACCEPTED_CORE_MAP.md` §5、`PACKAGING_BOUNDARY.md` §4 |
| 规范 FiniteBounds 源/对象 | 源 `16efff267512872cf33d612beb0e61d0feacd2fca3301c68350113f635d4b028`；对象 `78190e5fd4b4e4c642be6c19ff2e3d8293eaf037cb0fd28d03af4e4c9394bb12` | `PACKAGING_BOUNDARY.md` §4 |
| JetBounds 13 个修订模块 | P000–P011 + P061 绑定 **D39** 源与对象 | `C02/results/D39_SOURCE_PROVENANCE_CORRECTION.json` |

## 1. 冻结运行时（证书格式与验证器参考语义）

根：`/root/microscope_ws/rho5_deep500_all_open_20260910_08/runtime/deep500/v44/frozen/v41/`（X，只读）

| 文件 | SHA256 | 角色 |
|---|---|---|
| `dual_box.py` | `d396322514e6b2ced8caae02cae81664a6d8ce0b79a2fee3231561542fb9f0df` | `rows_and_bounds`（波行顺序）、`coefficients`/`bound_value`、`apply_wave`、`common_contract`（固定传播序）、`replay_trace` |
| `pivot_windows.py` | `e42100e5611bc8c18bee918687892669d84658adb7921ed8aaf686dac2a8b0cc` | `WINDOW_ROWS`、`PACKS`、`cycle_rows` |
| `source_access.py` | `7c1160a34dcbf4d33523734546670fda0d263fb7aa95e09b907ecd910cf7ee42` | 只读来源访问与哈希校验入口 |
| `discovery.py` | `91eede9b51258ff93e1d1c6866117696d4794bcc9a6a49a06e1fdba39a4722d3` | 本阶段未细读其内容（`待核对`） |
| `v41_protocol.py` | `55ee6ae862e754691810578c8b5c4d77f92df87f69aace414cde0d014b30000c` | 本阶段未细读其内容（`待核对`） |
| `dependency/IDENTITY.json` | `dbf81847ef46f4f054354b01f1771e84d5e1780f789109666350ad5e992e1843` | 载荷身份：`received_zip_sha256 65e5bd5e7586fb9d1cd47324447ef06ac35f55e74ad76a1d1fa09e2aa8ebfa7d`、`reported_root_sha256 d350fc632f317f2a3f0c5dd60eb9506cd64ab5e83e636939b5266dbcf25eca31`、`b17_model_sha256 39a65f2cbd6089dab3a403c6a72f365a02003737a641be86c3cf73cb70e76de3`、**`unreceived_original_tree_replayed_here: false`** |
| `dependency/RHO5_ROUND50_V40_LIGHT.zip` | `65e5bd5e7586fb9d1cd47324447ef06ac35f55e74ad76a1d1fa09e2aa8ebfa7d`（6 520 765 B） | LIGHT 载荷（**原树不在其中**；`IDENTITY.json` 自述未接收/未重放） |

**可复现程度**：格式与验证器语义可读、可哈希核对；**完整载荷重放 = `NOT_RECEIVED`**（原树未接收）。
另注：C11 的 `BASE_ORACLE_RUNTIME_INPUTS.json` 记录它复用的 C08 绑定解析到 `v39/paths.py`，
外层 zip `65e5bd5e…`、内层 zip `5197e72293fdb7e893cb0d3c0e001a183004f0bf050d17d77802b0edc59fa2df`
（与本表同一外层 zip 哈希，可交叉核对）。

## 2. 计算模型与数据输入

| 材料 | 路径 | SHA256 |
|---|---|---|
| 新增 C 前缀（G02/G03 共用输入） | `work/codex-parallel/C10/inputs/V31_128_NEW_C_PREFIX.json` | `8de156adfc415fed14deb90539c725161a99b1262969b7574215ca5ba164a8f7` |
| 精确模型（22 坐标 / 35 乘积 / 106 行） | `work/codex-parallel/C10/inputs/mc_exact_model.json` | `5fb91ced098b36174e1f307f543cf30872a075f262d477bc2bdb378b39aa94c5` |
| 接受源 Model.lean（C10/C12 共用） | `work/codex-parallel/C10/inputs/accepted_source/Rho5/Shared/MainlineTreeCover/V31Batch/Model.lean` | `4f5f6b7d6357d2a8fb7c9b3f9f22fd453387a1d9f9eb120136d7614318a09469` |
| C12 追加接受源 | `work/codex-parallel/C12/inputs/accepted_source/.../V31Batch/Leaf0{16..22}.lean` | 逐文件哈希见 `work/codex-parallel/C12/results/DATA_PROVENANCE.json`（本次未逐个复核） |
| M01 根前缀样本 | `/Users/mike/Documents/Codex/2026-09-07/rho5-mainline-v2/work/lean_mainline_tree_cover_20260912/V31_FIRST_PREFIX_SAMPLE.json` | `883ee574053f16c3b0923fee0429aad68f088282027fa713cedcbad3abfa142a`（由 M01 `READY.json` 声明） |
| C10 G02 原始字节 | C10 运行产物（`raw_g02_sha256`） | `572eea3d24abea5f46832c470f6b7576d5fc3ce868e98497a90e53edda64245d` |
| M02 G03 编译成本基线 | `outputs/research_alignment_20260912/M02_G03/G03_COMPILE_COST_BASELINE.json` | `5619637e0a553448bf2f06e0ba331fcb7480161621084644f0e1fa90c4adb48d`（由 C12 `BASELINE_ANALYSIS.json` 声明） |

## 3. 证书/回执与「它证明了什么」

| 回执 | 路径 | 声明要点（逐字核对自回执） | 哈希/数字 |
|---|---|---|---|
| C02 三阶段总装 | `outputs/relay_1345_delivery_20260912/C02/INTAKE_RECEIPT.json` | `ACCEPTED_SCOPED`；三门前述；**`exact XGlobalSafety and original D142 RootEndpointSafety remain unpaid`** | 8 模块；具名公理目标见回执 |
| M01 有限覆盖 | `…/lean_mainline_tree_cover_20260912/READY.json` | `PASS_FINITE_COVER_AND_ACTUAL_PREFIX_NOT_GLOBAL_CLOSURE`；`full_V31_closed: false`；8 前沿；0 终端义务 | 10 模块 / 65 具名公理检查 |
| M02 G01 | `outputs/relay_1408_delivery_20260912/M02_G01/{INTAKE_RECEIPT.json, BATCH_LEDGER.json}` | `ACCEPTED_SCOPED`/`V31_BATCH_REAL_EMPTY_READY`；5 叶；7 前沿；`actual_matrix_to_polynomial_bridge: EXTERNAL_OBLIGATION`；`full_V31: OPEN` | 27 模块 / 408 具名公理目标 |
| C09 小 k 五前沿 | `…/rho5-lean-staged-assembly/outputs/C09_actual_smallk_frontier/ACTUAL_SMALLK_FIVE_FRONTIERS_READY.json` | `READY`；关闭 `0000000/0000001/000001`；剩 5 前沿；输入仅三前提 | 源/olean/日志哈希与 exit 0 齐备 |
| C10 G02 内核 | `work/codex-parallel/C10/results/{INTEGER_DATA_PROVENANCE.json, INDEPENDENT_KERNEL_REVIEW.md}` | 21 节点；records 17–37；scale 4800；独立源审「无 soundness 缺口」，**不替代**编译回执与最终公理审计 | raw_g02 `572eea3d…` |
| C12 G03 | `work/codex-parallel/C12/{COMPUTE_FREEZE.json, results/GENERATOR_CONTROL_RESULTS.json}` | **`FROZEN`**；`EXTERNAL_ADAPTER_CONTROLS_PASSED_NOT_LEAN_PROOFS` | 冻结时刻 `2026-09-12T08:10:56Z` |
| C11 base oracle | `…/C11_base_oracle_gap/results/BASE_ORACLE_GAP_REAL_READY.json` | `COMPLETE`（scoped）；冻结运行时 `f159497cf5a767bbec10139219b28c4feaaa182241d7b063e9f4cf92bf1fc5ec`；`CertifiedBase.ofEmpty` 需先前排除证明 | 97 交付文件 / 48 定理检查 / 4368 import |
| C08 高值契约 | `…/outputs/C08_high_value_contract.delivery.json` | 9 模块 / 123 声明 / 73 定理；scope `high_value_contraction.contract only` | archive `b04e5ae2…`、ready `e18d2527…` |
| D134 B17 根界 | `work/dsh-main/parallel/D134/results/B17_ROOT_BOUNDS_READY.json` | 17 条闭根界；headline `root_of_normalizedB_high` | 7 模块 / 21 具名公理打印 |
| D141 实际 ProperB→根 | `work/dsh-main/parallel/D141/results/ACTUAL_PROPER_B_ROOT_READY.json` + `outputs/assembly_intake_20260912/D141/INTAKE_RECEIPT.json` | `ACCEPTED_FOR_ASSEMBLY_WITH_EXPLICIT_PREMISES`；保高 | 4 源哈希 / 8 live binding / 11 公理 |
| D142 容量端点 | `work/dsh-main/parallel/D142/results/B_ROOT_CAPACITY_ENDPOINT_READY.json` + `outputs/assembly_intake_20260912/D142/INTAKE_RECEIPT.json` | 同前；**`RootEndpointSafety` 仍未付** | 4 源哈希 / 23 live binding / 5 公理 |
| D135 checker 真实语义 | `work/dsh-main/parallel/D135/results/CERTIFICATE_RULES_{REAL_SOUNDNESS_READY, SCOPE_CORRECTION}.json` | 实数域排除；**并明确更正** stage-A 只量词化有理点 | — |
| D136 实际 X 行/根盒 | `work/dsh-main/parallel/D136/results/X_V31_ACTUAL_MATRIX_106_ROWS_READY.json` 等 | 106 行 + 22 维根盒为结论 | — |
| D148 实际矩阵→模型来源 | `work/dsh-main/parallel/D148/results/X_SMALLK_ACTUAL_MATRIX_V31_MODEL_ENTRY_READY.json` | 三前提 → 真实同高代表 + `SameSource` + 实际原根 + 剩余前沿 | 6 模块 / 85 具名公理记录（D153 卡）等 |
| D153 动态 cycle 波 | `work/dsh-main/parallel/D153/results/DYNAMIC_CYCLE_WAVE_PROPAGATION_REAL_READY.json` | 运行规则实现（真实波序、动态 m、C07/C03 后处理、同点保留、EMPTY 消费） | 6 模块 / 85 具名公理记录 |

## 4. X 对象根与可迁移构建

| 用途 | 路径 | 备注 |
|---|---|---|
| 规范 C02 闭包 | `/root/microscope_ws/rho5_codex_c02_assembly_20260912/rebuild_01/build` | 不重用旧初次 C02/D142 根 |
| C04/C07 装配 | `/root/microscope_ws/rho5_codex_c02_assembly_20260912/{c04,c07}/…` | C07 构建根为 `/root/microscope_ws/rho5_codex_c02_assembly_20260912/c07/build`（D153 实际消费，0 冲突） |
| C01/C03/C05/C06 | `/root/microscope_ws/rho5_codex_c01_contraction_20260912/{build,c03,c05,c06}` | D153 staging 0 冲突 |
| 各 DSH 卡 | `/root/microscope_ws/rho5_lean_dsh_20260911/{D135,D136,D140,D141,D142,D143,D147,D148,D153}` | 各自 `build/lib/lean`、`tools/`、`results/` |
| M01/M02 | `/root/microscope_ws/mainline_v31_tree_cover_20260912{,/m02}` | M02 构建根含 27 模块 |
| 第三方缓存 | `/root/microscope_ws/rho5_lean_pilot_20260911/{project,.lake/packages}` | 精确 `LEAN_PATH` 以各卡成功构建记录为准 |

## 5. 运行说明的可得性（诚实标注）

* **有完整运行说明**：C02（`tools/build.py` 需按 `PACKAGING_BOUNDARY.md` §4 指定 `rebuild_01`）、
  D153（`tools/d153_build.sh` + `d153_run_lean.py`，含 staging/守卫）、各 DSH 卡 driver。
* **只有成功日志与哈希、无独立运行脚本**：C10/C11/C12 的批次执行（回执内有 log 路径与 sha256，脚本本体未在本索引内定位 = `待核对`）。
* **参考实现（Python）可读但非 Lean 验证器**：冻结运行时（§1）。
* **载荷不可得**：原 V31 树（`unreceived_original_tree_replayed_here: false`）⟹ 完整重放 = `NOT_RECEIVED`。

## 6. 本索引的边界

本次**未**执行：任何 Lean 编译、任何 Python 证书重跑、任何压缩包全量展开、任何树扫描。
所有哈希要么来自上述回执/JSON 的既有字段，要么由本会话对具名文件直接 `sha256sum` 得到（§1 六项 + §0 引用项）。
未在本索引出现的材料一律视为**未核**，不得据其推断全域结论。
