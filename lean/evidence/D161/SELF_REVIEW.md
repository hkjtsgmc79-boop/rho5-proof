# SELF_REVIEW — D161（第一阶段使用示例与构建说明）

范围：本卡新增的两个 Lean 文件、两份文档与回执。**不**重审 C02/D84/任何上游数学；
上游结论按其已接收回执与最终绑定复用。

## 1. 本次实际新增并核验的内容

| 项 | 证据 |
|---|---|
| `Rho5.PhaseOne.Examples`（12 个 theorem/example） | X 上真实编译 exit 0，6.011 s，峰值 RSS 4.26 GB，ole an `2e9619f7…` |
| `Rho5.PhaseOne.ExamplesAudit`（13 `#check` + 12 `#print axioms`） | X 上真实编译 exit 0，6.010 s，峰值 RSS 1.74 GB，olean `74280f63…` |
| 源/对象/日志哈希 | `RELEASE_READY.json`、`SHA256SUMS`（本地与 X 逐位一致） |
| 依赖解析绑定 | `results/GATE_BINDING.json`：Examples 40 模块 / Audit 41 模块，`missing_oleans` 为空 |
| import 边界 | 唯一 import 是 C02 `Conditional` ⇒ 闭包 ⊆ C02 记录的 Conditional 闭包（495 源节点 / 4788 对象），未做第二次全依赖重扫；名称模式命中 0 |

## 2. 公理与禁用项

* 12 条 `#print axioms` 全部为 `{propext, Classical.choice, Quot.sound}`；`sorryAx` 出现 **0** 次。
* 两个新源文件不含 `axiom`/`sorry`/`admit`/`native_decide`（grep 复核见下）。
* **没有**无条件 `rho5Trace = α` 的示例；`rho5Trace_eq_alpha` 的两个参数在公开类型里可见。

```text
$ grep -nE "\b(axiom|sorry|admit|native_decide)\b" src/Rho5/PhaseOne/*.lean
（无输出）
```

## 3. 复用的既有证据（未重做）

* C02 修订接收：`INTAKE_RECEIPT.json`（ACCEPTED_SCOPED，三门前已接收）、8 模块成功记录、
  9 个具名标准公理检查——本次只读引用。
* 完整公开类型：`results/FULL_TARGET_TYPES.txt`——本卡示例的每个被调用定理都先在此核对
  （`#check` 输出亦随审计日志保存）。
* 锁与 pin：`lake-manifest.json` 的 SHA256 本次在 X 上**独立复核**，与 `PACKAGING_BOUNDARY.md`
  记录的 `6fa600a6…` 一致；mathlib pin 取自 C02 绑定文件 `c5ea0035…`。
* C02 对象根：`rebuild_01/build` 的 930 个 olean 以符号链接进入本卡根，**未重编**。

## 4. 明确未做 / 未知

| 项 | 状态 |
|---|---|
| 干净机器（fresh machine）从零构建 495 模块源码闭包 | **未做**，无此测量 |
| 干净机器构建 mathlib（无 cache） | **未做**（数小时级） |
| Mac 或任何非 X 平台编译 | **未做**；本阶段所有 Lean 运行在 X |
| 阶段二树/检查器/样本实例的编译或复用 | **未做**，也不在本卡默认入口 |
| `hX`/`hB` 的任何证明、近似或外部替代 | **未做**，类型保持原样未弱化 |

## 5. 边界声明（与 USAGE.md 一致）

本阶段交付"已验来源桥 + 条件 sharp 终点"。**不能**据此声称计算机辅助证明已完整：
`XGlobalSafety` 与 `RootEndpointSafety` 未付，外部计算的 PASS/有限样本不会自动转成它们的证明。
示例文件是既有定理的使用示例，本身不含新数学。

## 6. 资源与过程

* 每模块编译前 preflight：`MemAvailable` 79 GiB（≥ 16 GiB）、磁盘 15 GiB（≥ 10 GiB）；
  `nice 10`、`-j1 -M8192`、AS 12 GiB、RSS 8 GiB 看门狗未触发；同一时刻仅本 owner 一个 Lean。
* 过程处置：只做覆盖写、符号链接与 `mv`（探针文件 `Probe.lean` 从 `src/` 移到 `tools/probes/`，留作证据）；
  **未删除任何文件**；未改共享 STATUS/队列/他人文件；未触碰 D160 的 lakefile/manifest。

## 7. 交付路径状态（精确缺项）

卡面要求交付到 `outputs/phase1_noncomputational_assembly_20260912/D161/`。本会话文件沙箱为
workspace-write：对该目录子目录的 `mkdir` 被拒绝（`Operation not permitted`）。按 DSH 规则只重试一次并
申请更宽权限，**申请被拒绝**，因此不再尝试、也不绕行（AGENTS.md 亦规定 `outputs` 归协调者维护）。

已完成产物全部在：

* 工作区：`work/dsh-main/parallel/D161/`（USAGE.md、BUILDING.md、RELEASE_READY.json、SELF_REVIEW.md、
  SHA256SUMS、`src/Rho5/PhaseOne/{Examples,ExamplesAudit}.lean`、`results/GATE_BINDING.json`、`logs_x/*.log`）；
* X：`/root/microscope_ws/rho5_lean_dsh_20260911/D161/`（同内容 + 编译对象与驱动）。

协调者只需把上述文件复制进卡面目录即可完成发布（命令见 `RELEASE_READY.json` 的 `delivery.coordinator_action`）。
