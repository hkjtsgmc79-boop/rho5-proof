# D159 自审

2026-09-12。卡：`parallel/D159/TASK.md`（第一阶段：外部计算责任与来源覆盖交接表）。

## 1. 本次实际做了什么（可复核）

* 逐字读取两个总责任的**原文 Prop**：`XGlobalSafety`（`C02/src/Rho5/Integration/StagedAssembly/Conditional.lean:16`）、
  `RootEndpointSafety`（`work/dsh-main/parallel/D142/src/Rho5/Shared/BRootCapacityEndpoint/Refutation.lean:37`），
  以及条件终点的消费点（`rho5Trace_eq_alpha_of_safety`）。
* 读取卡指定的两份前置文档：`ACCEPTED_CORE_MAP.md`（全篇）与 `PACKAGING_BOUNDARY.md`（§1–§6）。
* 有界读取既有回执/索引（**未**做任何全量扫描）：
  `C02/INTAKE_RECEIPT.json`、M01 `READY.json`、M02_G01 `INTAKE_RECEIPT.json`+`BATCH_LEDGER.json`、
  C09 `ACTUAL_SMALLK_FIVE_FRONTIERS_READY.json`、C10 `INTEGER_DATA_PROVENANCE.json`+`INDEPENDENT_KERNEL_REVIEW.md`、
  C12 `COMPUTE_FREEZE.json`+`DATA_PROVENANCE.json`+`GENERATOR_CONTROL_RESULTS.json`、
  C11 `BASE_ORACLE_GAP_REAL_READY.json`+`BASE_ORACLE_RUNTIME_INPUTS.json`+`C11_ACTUAL_IMPORTS.json`、
  C08 delivery JSON、C04 `LIFTED_TRACE_SOURCE_FRONTIER_ASSEMBLY_READY`、D134 `B17_ROOT_BOUNDS_READY.json`+`BUILD_STATUS.json`、
  D141/D142 intake receipts、D135 两个 CERTIFICATE_RULES 回执、D140 `PHASE1_FROZEN.json`+`firstwave_paid_gate.json`、
  `work/dsh-main/tasks/DISPATCH_QUEUE.json`（策略字段）。
* 直接 `sha256sum`（本会话实测，非引用）：冻结运行时 5 个 `.py`、`dependency/IDENTITY.json`、
  `dependency/RHO5_ROUND50_V40_LIGHT.zip`（见 `REPRODUCIBILITY_INDEX.md` §1）。
* 逐字核对运行时与 Lean 的**波序/传播序**：`dual_box.py` 39–63 行与 `common_contract` 22 行 ⟷ D153 的
  `wavePolynomials`/`propagationPolynomials`（本阶段新核对项，非复用声明）。

## 2. 本次明确**没有**做

* 未调用 Lean（本卡无需编译的文档工作，按卡不启动 Lean）；
* 未重跑任何外部证书/检查器，未展开压缩包全量，未扫描千万树，未复开任何旧计算任务；
* 未修改或复制任何 Lean 源，未改共享 `STATUS`/队列/他人文件，未删除任何文件；
* 未做第二次数学重审（全部引用原 owner 自审与正式回执）。

## 3. 分类纪律自检

每一行都落在 `REDUCTION_PROVEN` / `COMPUTE_RECEIPT` / `PAYLOAD_REPLAY` / `WIRING_OPEN` 四类中，并可并列。
逐项自查：

* **没有**由叶数或局部 PASS 宣称 `hX`/`hB`（X6 行明写 `full_V31_closed: false`、7–8 条前沿未闭合）；
* **没有**把 Python `PASS`/`check=true` 当证明（C12 行逐字保留 `EXTERNAL_ADAPTER_CONTROLS_PASSED_NOT_LEAN_PROOFS`）；
* **没有**把分支级结论（`high_value_contract.contract`、`oracle_from_base`、小 k 分支、首 C、M02 五叶）写成全域；
* **没有**把 `y → zStar` 描述成又一次符号共轭（B4 行明确写成同框 canonical 构造）；
* **没有**把条件终点写成无条件 `rho5Trace = alpha`（§0 与 §6 两处明写）。

## 4. 交付位置：精确错误与处理

卡要求交付到 `outputs/phase1_noncomputational_assembly_20260912/D159/`。本会话沙箱为 `workspace-write`，
该路径在工作区之外，写入被拒：

```
[denied] write outputs/phase1_noncomputational_assembly_20260912/D159/EXTERNAL_COMPUTATION_OBLIGATIONS.md
         -> Error: [sandbox: file access denied under workspace-write mode]
[retry with sandbox_permissions=danger-full-access, justification given]
         -> Error: the user rejected escalating this operation to "danger-full-access"
```

按「被拒后不得用替代路径绕过」的规则，我没有改用 bash/其它路径写入该目录。全部产物现落在本卡独占工作目录
`work/dsh-main/parallel/D159/`，**内容完整、文件名与卡要求一致**；移入交付目录（或授权后重写）属协调者/用户动作。

## 5. 待核对（不猜、不伪造关联）

1. 原树载荷：`IDENTITY.json` 自述 `unreceived_original_tree_replayed_here: false` ⟹ 全域重放 `NOT_RECEIVED`；原树来源待核对。
2. C11 `oracle_from_base` 域与 `IsRootCapacityEndpoint` 全域是否同一 `NormalizedB` 域：无回执 ⟹ 待核对。
3. C09 的 5 前沿与 M02 的 7 前沿：列表可对照，无正式并轨回执 ⟹ 待核对。
4. 冻结运行时与 Lean 的解析器/可执行等价：未形式化（波序/传播序已核对，属两回事）。
5. C06 runtime strict、C13：本阶段未读其回执 ⟹ 待核对。

## 6. 复用 vs 新增（本次区分）

| 类别 | 内容 |
|---|---|
| **本次新增核验** | 冻结运行时 7 个文件的 sha256；两处原文 Prop 的行号定位；波序/传播序的逐字对照；本表与索引的组织与分类 |
| **复用（未复核其数学）** | 上述所有 Lean 回执的证明内容与具名公理记录、各卡 owner 自审、C10/C11/C12/C08 的计算结论、M01/M02/C09 的既有门 |

## 7. 结论

本卡交付的是**外部计算依赖的准确对应与缺口登记**，不是新的证明、不是全域结论、不是对任何计算回执的再验证。
`hX`/`hB` 仍未付；第一阶段可以交付条件主线（`rho5Trace_eq_alpha_of_safety hX hB`），但不得改名为无条件结果。
