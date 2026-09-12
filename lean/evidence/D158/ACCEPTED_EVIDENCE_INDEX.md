# D158 — ACCEPTED_EVIDENCE_INDEX / 已接收证据与可迁移路径索引

用途：给总装者（D160 源码包、D161 使用示例、专用 Codex 最终组装）足够的引用依据：**哪条结论、看哪份回执、迁移时该带哪些相对路径**。
本索引只列已接收回执与少量核心类型/公理文件；**不搬历史日志海量**，不复制全源码。所有路径以仓库根 `rho5-lean-formalization/` 为基准写成可迁移相对路径（`outputs/...`），绝对路径仅在 `absolute_path` 字段保留，便于本地核对。

---

## 0. 默认主线证据（C02 修订接收）

| 用途 | 相对路径 | 绝对路径 | 状态 |
|---|---|---|---|
| 唯一正式 C02 接收回执（三门） | `outputs/relay_1345_delivery_20260912/C02/INTAKE_RECEIPT.json` | `/Users/mike/Documents/Codex/2026-09-11/rho5-lean-formalization/outputs/relay_1345_delivery_20260912/C02/INTAKE_RECEIPT.json` | `ACCEPTED_SCOPED`；`ASSEMBLY_BASELINE_READY`、`ASSEMBLY_X_B_ROOT_REDUCTION_READY`、`ASSEMBLY_CONDITIONAL_ENDPOINT_READY` |
| 三门各自 READY | `outputs/relay_1345_delivery_20260912/C02/results/ASSEMBLY_{BASELINE,X_B_ROOT_REDUCTION,CONDITIONAL_ENDPOINT}_READY.json` | 同上目录 | 三门 |
| **完整编译器公开类型**（引用依据，勿重 print 全库） | `outputs/relay_1345_delivery_20260912/C02/results/FULL_TARGET_TYPES.txt` | 同上 | 9 个具名目标 + 公理行 |
| 具名标准公理记录 | `outputs/relay_1345_delivery_20260912/C02/results/AXIOM_RECORDS.json` | 同上 | 9 个目标 |
| 8 模块当前成功记录（源/olean 哈希） | `outputs/relay_1345_delivery_20260912/C02/BUILD_STATUS.json` | 同上 | `ALL_THREE_SCOPED_STAGES_READY` |
| 最终 import 与规范源/对象配对（迁移白名单） | `outputs/relay_1345_delivery_20260912/C02/results/IMPORT_SOURCE_OLEAN_BINDING.json` | 同上 | `source_closure` 495 条；`lake_manifest_sha256 = 6fa600a6…` |
| 依赖登记（哪些已验但未导入） | `outputs/relay_1345_delivery_20260912/C02/DEPENDENCIES.json` | 同上 | 含 `ACCEPTED_AVAILABLE_NOT_IMPORTED` |
| 依赖修订依据（不重审数学） | `outputs/relay_1345_delivery_20260912/C02/results/REBUILD_REVIEW.json`、`.../results/D39_SOURCE_PROVENANCE_CORRECTION.json` | 同上 | 42 次必要重编 + 13 个 JetBounds 来源修正 |
| 原 owner 修订包（可选追溯） | `outputs/../2026-09-12/rho5-lean-staged-assembly/outputs/C02_staged_assembly_rebound/` | `/Users/mike/Documents/Codex/2026-09-12/rho5-lean-staged-assembly/outputs/C02_staged_assembly_rebound/` | 修订来源；**旧 `C02_staged_assembly` 预交付不作迁移源** |

**规范 X 对象根**（路径优先顺序：新增薄入口根 → 本根 → 第三方缓存）：
`/root/microscope_ws/rho5_codex_c02_assembly_20260912/rebuild_01/build`

---

## 1. 上游组件回执（A / B 类）

| 组件 | 回执相对路径 | 状态 | 本卡 `evidence/` 副本 |
|---|---|---|---|
| alpha 根身份 | `outputs/d09_alpha_independent_20260911/COORDINATOR_RECEIPT.json` | `independent_alpha_module_return_evidence_matched` | `evidence/D09_COORDINATOR_RECEIPT.json` |
| 候选/alpha 桥 | `outputs/d34_actual_alpha_bridge_20260912/INTAKE_RECEIPT.json` | `ACCEPTED_IMPLEMENTER_SELF_REVIEW_REUSED` | `evidence/D34_INTAKE_RECEIPT.json` |
| 原系统唯一性 / 实际 alpha 门 | `outputs/heartbeat_0420_delivery_20260912/D30/results/{ORIGINAL_READY,ALPHA_READY}.json` | `ORIGINAL_READY` / `ALPHA_READY` | `evidence/D30_ORIGINAL_READY.json`、`evidence/D30_ALPHA_READY.json` |
| 达到性 | `outputs/external_three_returns_20260912/accepted/D82/INTAKE_RECEIPT.json` | `ACCEPTED_DECLARED_SCOPE` | `evidence/D82_INTAKE_RECEIPT.json` |
| 范围/达到门 | `outputs/heartbeat_0748_delivery_20260912/D92/results/{GLOBAL_RANGE_READY,GLOBAL_ATTAINED_READY}.json` | 两门 | `evidence/D92_*` |
| 前四 pivot/第五归约 | `outputs/heartbeat_1019_delivery_20260912/D124/INTAKE_RECEIPT.json` | `ACCEPTED_DECLARED_SCOPE` | `evidence/D124_INTAKE_RECEIPT.json` |
| 完整第四 pivot（上游） | `outputs/heartbeat_0658_delivery_20260912/D86_FULL/INTAKE_RECEIPT.json` | `ACCEPTED_FULL_A_AND_B` | `evidence/D86_INTAKE_RECEIPT.json` |
| Physical X ↔ 矩阵/路径 | `outputs/heartbeat_0923_delivery_20260912/D103_FULL/INTAKE_RECEIPT.json` | `ACCEPTED_A_AND_B_FULL_SCOPE` | `evidence/D103_INTAKE_RECEIPT.json` |
| 最大者 → X/B | `outputs/g05_local_takeover_20260912/D131/INTAKE_RECEIPT.json` | `ACCEPTED_DECLARED_SCOPE_OWNER_COMPILATION_REVIEW_REUSED` | `evidence/D131_INTAKE_RECEIPT.json` |
| X/B 下层 | `outputs/g05_local_takeover_20260912/D126/INTAKE_RECEIPT.json` | `ACCEPTED_DECLARED_SCOPE` | `evidence/D126_INTAKE_RECEIPT.json` |
| B 根入口 | `outputs/assembly_intake_20260912/D141/INTAKE_RECEIPT.json` | `ACCEPTED_FOR_ASSEMBLY_WITH_EXPLICIT_PREMISES` | `evidence/D141_INTAKE_RECEIPT.json` |
| 容量端点 | `outputs/assembly_intake_20260912/D142/INTAKE_RECEIPT.json` | `ACCEPTED_FOR_ASSEMBLY_WITH_EXPLICIT_PREMISES` | `evidence/D142_INTAKE_RECEIPT.json` |
| 容量桥 | `outputs/progress_1204_delivery_20260912/D139/INTAKE_RECEIPT.json` | `ACCEPTED_SCOPED_CARD` | `evidence/D139_INTAKE_RECEIPT.json` |
| 解析轨迹（本阶段有限新增） | `outputs/heartbeat_0807_delivery_20260912/D84/INTAKE_RECEIPT.json` | `ACCEPTED_DECLARED_SCOPE` | `evidence/D84_INTAKE_RECEIPT.json` |
| 可选：资源逃离 | `outputs/heartbeat_0835_delivery_20260912/D100/INTAKE_RECEIPT.json` | `ACCEPTED_DECLARED_SCOPE` | `evidence/D100_INTAKE_RECEIPT.json` |
| 可选：紧集边界 | `outputs/heartbeat_0857_delivery_20260912/D108/INTAKE_RECEIPT.json` | `ACCEPTED_DECLARED_SCOPE` | `evidence/D108_INTAKE_RECEIPT.json` |
| 终点等价接口 | `outputs/heartbeat_0748_delivery_20260912/D96/results/FINAL_ASSEMBLY_INTERFACE_READY.json` | `CONDITIONAL_ENDPOINT_INTERFACE` | `evidence/D96_FINAL_ASSEMBLY_INTERFACE_READY.json` |

---

## 2. 迁移时必须携带的相对路径（给 D160 / 最终总装）

1. **产品薄入口根**（本阶段新增）：`Rho5/Phase1/**`（建议名，D160 定；仅导入 C02 `Conditional` 与 D84 `PhysicalTrip`）。
2. **项目源码闭包**：以 C02 `results/IMPORT_SOURCE_OLEAN_BINDING.json` 的 `source_closure`（495 条）为模块白名单；保留原公共聚合 `Rho5/Integration/StagedAssembly.lean` 时再 +1（496）。每模块**只留一个规范版本**。
3. **D84 实际新增边**：`Rho5/ExternalV43Existence/**` 及其在绑定中真实新增的模块；不得因此扩大扫描范围。
4. **第三方 pin**：Lean `4.30.0` / `d024af099ca4bf2c86f649261ebf59565dc8c622`；mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`；`lake-manifest.json` SHA256 `6fa600a652ca1ef77814e08127d1078febb38e3018ed9f8b1c5683b92427b789`。**不复制** mathlib、Lean runtime、所有 `.lake` 缓存、其它任务工作目录或历史日志。
5. **审计入口单独存在、不进入产品默认 import**（C02 四个 Audit 文件与新增审计薄入口）。
6. **证据打包**：本目录 `evidence/` + 被引用的成功日志（少量）+ 公开类型输出；完整历史证据保留引用目录即可。

**冲突解决**：同名模块一律按 C02 最终 source/olean 绑定，不按目录最近修改时间或搜索路径“先找到哪个就用哪个”；FiniteBounds 用规范 D120 源/对象（`16efff26…`/`78190e5f…`），JetBounds P000–P011 与 P061 共 13 个绑定 D39 源。

---

## 3. 与 D159 的接口（不重复登记）

| 全域安全 ID | 定义处（类型出处） | D158 登记 | D159 责任 |
|---|---|---|---|
| `XGlobalSafety` | C02 `Conditional`；类型原文见 `FORMALIZATION_COVERAGE.md` §3.1 | 接口、精确 Prop、未付状态、方向说明 | 原始计算证书/树覆盖的**溯源**与消费链 |
| `RootEndpointSafety`（原 D142） | `Rho5.Shared.BRootCapacityEndpoint.Basic`；类型原文见 §3.2 | 同上 | 同上 |

两份全域安全 ID 在 `THEOREM_CATALOG.json` 中的 `receipt.cross_reference` 均指向 D159；本卡**不**重复其证书溯源工作。

---

## 4. 本次新增核验 vs 复用证据

* **本次新增核验（D158 自己做的）**：① 逐一确认上表回执文件存在并读出其真实状态字符串；② 对 12 组上游组件做了声明名抽查（共 34 个名字，33 命中，1 组归属修正为 D141/D142，详见 `SELF_REVIEW.md`）；③ 复核 C02 的 9 个公开目标名与编译器输出一致；④ 复核 `lake_manifest_sha256`、`source_closure` 条目数（495）与三门 READY 文件的存在性。
* **复用的证据**：D09/D34/D30/D82/D92/D124/D86/D103/D131/D126/D141/D142/D139/D84/D100/D108/D96/C02 的 owner 自审与协调者接收回执；C02 的 `FULL_TARGET_TYPES.txt`、`AXIOM_RECORDS.json`、`BUILD_STATUS.json`、`IMPORT_SOURCE_OLEAN_BINDING.json`。
* **未做（明确）**：未调用 Lean；未编译；未重跑任何证书；未重审数学；未全库/依赖重扫；未复制全源码；未改动任何共享文件、任务队列或他人目录。
