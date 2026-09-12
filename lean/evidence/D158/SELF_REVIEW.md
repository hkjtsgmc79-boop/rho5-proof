# D158 — SELF_REVIEW / 自审（本次新增核验 与 复用证据分离）

范围：`parallel/D158/TASK.md` 第一阶段非大规模计算总装准备。本卡**未调用 Lean、未编译、未重跑证书、未重审数学、未全库扫描**。以下自审只覆盖“本卡实际做了的核验”。

## 1. 交付完整性

| 卡片要求 | 产物 | 状态 |
|---|---|---|
| 四类覆盖清单（无条件/保留参数/未形式化来源/延后计算），含实际 alpha、候选存在唯一性、达到、粗界、全局最大者、前四 pivot、X/B 归约、真实解析轨迹 | `FORMALIZATION_COVERAGE.md` | 完成（文档分 A1–A8、B1–B3、C1–C4 与 D 节；与目录 20 项一一对应：A 9 / B 5 / C 3 / D 2；§5 专列解析轨迹定位） |
| 逐项稳定 ID/模块/真实公开名/前提结论/回执与类型出处/默认入口 | `THEOREM_CATALOG.json` | 完成（20 个 item；见 §2 抽查） |
| 可迁移相对路径 ↔ 现有回执映射；少量核心回执副本 | `ACCEPTED_EVIDENCE_INDEX.md` + `evidence/`（26 个文件，168 KB） | 完成 |
| RELEASE_READY / SELF_REVIEW / SHA256SUMS | 本文件、`RELEASE_READY.json`、`SHA256SUMS` | 完成 |
| 不重复 D159；全域安全 ID 交叉引用 | `ACCEPTED_EVIDENCE_INDEX.md` §3、`THEOREM_CATALOG.json` 的 `SAFETY.*.receipt.cross_reference` | 完成 |
| 不复制全源码、不写新证明、不做使用示例 | 未复制任何 `.lean`；未新增定理；未写示例 | 遵守 |

## 2. 声明名抽查（本次新增核验）

对每个被引组件，在其交付目录的源码/回执文本中检索该组件的公开声明名。结果（实际执行记录）：

| 组 | 检索名数 | 命中 | 说明 |
|---|---:|---:|---|
| D84 `ExternalV43Existence` | 6 | 6 | `exists_actual_trajectory` 等 |
| D09 `AlphaRoot` | 7 | 7 | 根身份 7 名全中 |
| D34 | 1 | 1 | `candidate_system_eq_actual_alpha` |
| D30 | 3 | 3 | 原系统唯一性/alpha 临界元组 |
| D82 | 3 | 3 | 达到性三名 |
| D92 | 4 | 4 | 范围/达到四名 |
| D124（+D86 上游） | 3 | 3 | 前四 pivot 与第五归约 |
| D103_FULL | 4 | 4 | `legalTrace_M` 等 |
| D131 | 2 | 2 | `exists_global_ts_maximizer`、`exists_global_max_X_or_properB` |
| D126 | 2 | 0 → 2 | **归属修正**：`actual_properB_high_has_root_representative`、`root_capacity_endpoint` 不在 D126，而在 D141/D142；D126 实际含 `ActualXBReduction`/`CanonicalXB`（已另测 2/2 命中）。目录已按修正写入 |
| D141 | 2 | 2 | B 根入口 |
| D142 | 3 | 3 | 容量端点 + `RootEndpointSafety` |
| D139 | 3 | 3 | 容量桥 |
| D100 | 3 | 3 | 可选资源逃离 |
| D108 | 3 | 3 | 可选紧集边界 |
| D96 | 1/3 期望命中 | 1 | `FINAL_ASSEMBLY` 命中；`XGlobalSafety`/`RootEndpointSafety` 本就不在 D96（定义在 C02），符合预期 |
| C02 编译器目标名 | 9 | 9 | 与 `FULL_TARGET_TYPES.txt` 逐名一致（含 `legal_growth_le_alpha_via_fifth_of_safety`） |

合计 17 组、52 个名称探针；除上述 1 组归属修正外全部命中，修正后无遗留未命中项。

## 3. 事实一致性核对（本次新增核验）

| 核对项 | 依据 | 结果 |
|---|---|---|
| C02 三门接收 | `C02/INTAKE_RECEIPT.json` | `ACCEPTED_SCOPED`，三门 `ASSEMBLY_*_READY` 齐备 |
| C02 具名标准公理目标数 | `INTAKE_RECEIPT`（9）与 `AXIOM_RECORDS.json`、`FULL_TARGET_TYPES.txt` 的公理行 | 一致（9） |
| C02 模块数 | `INTAKE_RECEIPT`（8）与 `BUILD_STATUS.json` 的 `modules`（8） | 一致；源/olean 哈希已入 `ACCEPTED_EVIDENCE_INDEX.md` 引用 |
| 迁移白名单规模 | `IMPORT_SOURCE_OLEAN_BINDING.json` | `source_closure` = 495；脚本读出条目数与地图 §2（495/496）一致 |
| 固定环境 | 同上 + `PACKAGING_BOUNDARY.md` | `lake_manifest_sha256 = 6fa600a652ca1ef77814e08127d1078febb38e3018ed9f8b1c5683b92427b789`，Lean/mathlib commit 一致 |
| 上游回执状态 | 17 份回执 | 全部存在且状态与地图一致（D141/D142 = `ACCEPTED_FOR_ASSEMBLY_WITH_EXPLICIT_PREMISES` 等） |

## 4. 明确未核验 / 未知（Write as unknown）

1. 未核验 C02 闭包以外的任何下游消费点，也未核验“是否存在把全部实际相关源一次接入完整检查域/根覆盖的现成组合定理”；清单中已按“未知/未付”登记。
2. 未核验 D160/D161 的产物（源码包、使用示例），本卡不依赖它们。
3. 未对任何上游模块重新编译或重放；所有对象层面的可信度沿用原 owner 自审与协调者接收回执（本卡未做第二次数学审查）。
4. `evidence/` 只保存回执与类型文本；未保存原成功日志（避免搬运历史日志海量），日志引用留在原接收目录。

## 5. 边界与禁止事项复核

* 未新增 `sorry`/`admit`/项目公理/`native_decide`；未写任何 Lean 文件。
* 未把外部 PASS、Bool、有限样本或逐叶占位前提写成全域证明；`SAFETY.XGLOBAL`、`SAFETY.ROOT_ENDPOINT` 明确标为未付。
* 未声称无条件 `rho5Trace = alpha`、whole X 安全或 `alpha` 安全目标完成。
* `RootSpec`、根存在、候选临界点存在均按“已消除”登记，未重新列为欠账。
* 未修改共享 `STATUS`/队列/他人文件；未删除任何文件；未启动 Lean 或租用资源。

## 6. 交付路径说明（需协调者动作）

卡片指定交付目录为 `outputs/phase1_noncomputational_assembly_20260912/D158/`，该路径在会话沙箱之外，本会话写操作被拒（升级请求亦被用户拒绝）。经用户确认，本卡产物写入：

```
work/dsh-main/parallel/D158/deliverables/
```

请协调者将该目录内容原样复制到 `outputs/phase1_noncomputational_assembly_20260912/D158/`（`SHA256SUMS` 可直接校验）。`RELEASE_READY.json` 的 `canonical_path` 与 `produced_at` 字段记录了这两个路径。
