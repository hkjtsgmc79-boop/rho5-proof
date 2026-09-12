# D160 SELF_REVIEW — 第一阶段可迁移 Lean 源码闭包归集

日期：2026-09-12 · 卡片：`parallel/D160/TASK.md` · 暂存交付根：`work/dsh-main/parallel/D160/deliverable/`
（卡面交付路径 `outputs/phase1_noncomputational_assembly_20260912/D160/` 见文末「唯一缺项」）

## 逐条对照卡面

| # | 卡面要求 | 落实 | 证据 |
|---|---|---|---|
| 1 | 按 C02 最终 `IMPORT_SOURCE_OLEAN_BINDING.json` 的 `source_closure` 收齐 495 个必要 Rho5 模块，每模块一个规范版本 | 495/495 复制，源哈希与 binding `source_sha256` 逐项一致；每模块记录 binding 的 olean 路径与对象哈希 | `SOURCE_MAP.json::modules[group=c02_conditional_closure]`、`SOURCES_READY.json::copy_hash_verification` |
| 1b | 可额外包含原三行 StagedAssembly 聚合及明确审计，但注明默认关系 | 聚合 `Rho5.Integration.StagedAssembly` + 4 个审计（`Audit`/`BaselineAudit`/`RootReductionAudit`/`ImportAudit`）共 5 个模块已包含；`SOURCES_READY.json` 明确它们**不进**产品默认 import（默认为 `Conditional`） | `SOURCE_MAP.json::modules[group=c02_aggregate/c02_audit]`、`SOURCES_READY.json::boundaries.default_import` |
| 2 | 有限加入 D84 正式接收的 `Rho5.ExternalV43Existence.PhysicalTrip` 及相对闭包的确切新增项目模块 | 入口 + 8 个 `ExternalV43Existence.*` 源（含 receipt `sources_sha256` 校验）与 142 个新增模块（相对 495 闭包）；本地正则闭包与 D84 自身 `lean --deps` 的项目模块数 146 对齐（142 新增 + 4 重叠） | `SOURCES_READY.json::d84_increment`、`evidence/D84_INTAKE_RECEIPT.json`、`evidence/D84_BUILD_STATUS.json` |
| 2b | 优先 D84 已验依赖清单与本地可读源；只核新增触及的同名哈希，不重扫 mathlib | 增量源全部本地（D84 lane src / D109 owner 包 / `work/lean-pilot` 基线），未从 X 取任何文件；未扫描或编译 mathlib | `SOURCE_MAP.json::selection_rules`、`logs/package_run.log` |
| 3 | 保留 D120 FiniteBounds 与 D39 P000–P011/P061 共 13 个 JetBounds 修订，按最终 binding 选择；冲突不按 mtime | FiniteBounds 源哈希 `16efff26…`、对象 `78190e5f…`（= 卡面规范值）；13 个 JetBounds 逐项带 `source_conflict_resolution`（D39 owner olean 哈希一致） | `evidence/D39_D120_provenance.json`、`SOURCE_MAP.json::d39_jetbounds_and_d120_finitebounds` |
| 3b | 每项记源路径→项目相对路径、源哈希、已验对象哈希及证据出处 | 642 个模块每条都有 `source` / `project_path` / `source_pre_sha256` / `copied_sha256` / `expected_sha256` / `hash_evidence` / `olean` / `olean_sha256` / `candidates` | `SOURCE_MAP.json` |
| 3c | 保留 lean-toolchain、锁定 mathlib 的 lakefile、原 lake-manifest 及依赖 pin；锁文件原件不升级 | 三件原样复制；`lake-manifest.json` sha256 = `6fa600a6…` 与 binding `lake_manifest_sha256` 相同；mathlib rev `c5ea0035…`；`upgrade_performed=false` | `evidence/lake_pins.json`、`SOURCES_READY.json::fixed_environment` |
| 3d | 可迁移默认 Lake roots 用 `Rho5.PhaseOne`（由 Codex 写），本卡不创建该 Lean 模块 | 未创建任何 `Rho5/PhaseOne*.lean`；仅在 `SOURCES_READY.json::boundaries` 注明归属 | `RELEASE_READY.json::definition_of_done_check` |
| 4 | `SOURCES_READY.json` 给计数、复制哈希核验、未解决源/版本冲突、D84 增量 | 全部字段齐备：计数 495/142/5/642；复制后重算 642/642 一致、0 mismatch、0 missing；2 项未解决冲突（Geometry/Regularity 交付原件 vs 实际编译源）并给出决定与出处 | `SOURCES_READY.json`、`evidence/VERIFY.json` |
| 4b | 不打完整缓存或 mathlib/runtime，不重编现有 495 模块 | 仅复制项目 `.lean` 源与 3 个锁文件；未复制 `.lake`/mathlib/runtime；未调用 Lean、未重编、未重跑证书 | `logs/package_run.log`、`evidence/VERIFY.json` |
| 4c | 新产品入口与审计由唯一总装 Codex 负责，D161 独占 Examples | 未创建产品入口/审计模块；未触碰 `parallel/D161`、`outputs/.../D161` 或任何他人目录 | 本卡仅写 `parallel/D160/**` 与暂存交付根 |
| 4d | 源码归集要真正执行，不能只交计划 | 642 个文件已实际复制并逐文件核验；两次独立脚本（归集 + 复核）产出 JSON/日志 | `logs/package_run.log`、`logs/verify_run.log`、`evidence/VERIFY.json` |
| 5 | 交付 `RELEASE_READY.json`、`SELF_REVIEW.md`、相关产物及 `SHA256SUMS`，区分本次新增核验与复用证据 | 齐备；`SOURCES_READY.json::reused_vs_new` 明确列出复用回执证据与本次新增核验（复制后哈希重算、候选一致性比对、锁文件比对、闭包重算、独立复核） | `RELEASE_READY.json`、`SHA256SUMS` |
| 6 | 不新增 `sorry`/`admit`/项目公理/`native_decide` | 本卡只做文件搬运，未新增或修改任何 Lean 源；机械文本扫描（去注释后）命中数列于 `evidence/VERIFY.json::token_scan.code_hits`，注释中的自述（如「无 sorry、无新公理」）已区分 | `evidence/VERIFY.json` |
| 7 | 未核验事实写未知；不声称已完整 | `RELEASE_READY.json::not_claimed`、`SOURCES_READY.json::boundaries.not_claimed` 明确：未重编、未重跑、未逐字节验证 X 上 495 对象、完整 `XGlobalSafety` 与原 D142 `RootEndpointSafety` 仍未付 | 同上 |
| 8 | 碰到实质阻塞留精确缺项并说明 | 见文末「唯一缺项」：交付目录写入权限 | `RELEASE_READY.json::definition_of_done_check[8]` |

## 独立复核（新证据）

`tools/d160_verify.py` 是对归集脚本的**独立**复核（不复用其内存状态）：逐文件重算 sha256 与 `SOURCE_MAP.json` 比对、
组计数核对、静态 import 闭包检查（642 个模块的全部 `Rho5.*` import 均在包内，未解析项为空）、锁文件比对、
去注释后的禁用记号扫描、`SHA256SUMS` 全量核对。结论：`evidence/VERIFY.json::verdict`。

## 诚实限定

1. **未调用 Lean**：本卡范围是源码搬运与文档（卡面：「无需编译的文档与搬运不启动 Lean」）；包内没有新增对象哈希，
   所有 `olean_sha256` 都是 C02/D84 回执的**复用证据**，不是本次重算。
2. **增量模块的上游回执覆盖**：8 个 `ExternalV43Existence.*` 有 D84 receipt 哈希；其余 134 个增量模块只有复制时哈希
   （`hash_evidence = copy-time sha256`），其正确性依赖 `work/lean-pilot`（D84 X pilot 构建的本地只读镜像）与
   D109 owner 包的一致性（两处并存时哈希相同，已记录）。
3. **两项同名冲突**：`Rho5.ExternalV43Existence.Geometry`/`Regularity` 的交付原件与实际编译源不同，
   按 D84 receipt/BUILD_STATUS 选**实际编译源**（交付原件哈希亦已记录，可切换）。
4. **闭包方法是本地正则 import 传递**（归集用途）；与 D84 的 `lean --deps` 计数一致，但不替代 Lean 自身解析。
5. **未做全库扫描**：未重新扫描 mathlib/全项目源码，未改写任何输入源或 assembly 工程。

## P01 校准（2026-09-12 最终调整）

默认来源集按 `work/codex-parallel/P01/results/ACTUAL_NEW_UPSTREAM_MODULES.json` 校准：
**C02 Conditional 495 + P01 真实新增上游 138 + 产品 `Rho5.PhaseOne` 1 = 634**
（= P01_THIN_READY.json 的 `loaded_Rho5 = 634`；`missing_from_C02 = 0`）。

本包提供其中 **633** 个模块源（产品模块由总装 Codex 提供，本包不创建）。包内另有 **9 个非默认模块**保留供复查并已显式标注：
D84 lane 伞/审计 4（`Rho5.ExternalV43Existence`、`.Audit`、`.LayerAudit`、`.Smoke`）、C02 三行聚合 1、C02 审计 4；
`default_set=false`，不进产品默认 import，默认 roots 可只取 `default_set=true` 的 633 个模块。

## 交付落地记录

卡面输出位置已更正为**本卡工作区** `work/dsh-main/parallel/D160/deliverable/`；本卡不再请求放宽权限、不再复制到
`outputs/`，最终搬运由协调者负责。自审回执见 `SELF_REVIEW_RECEIPT.json`。早前一次经批准复制到
`outputs/phase1_noncomputational_assembly_20260912/D160` 的副本已被本次重标定取代（本卡不删除它）。
`SHA256SUMS` 相对包根。
