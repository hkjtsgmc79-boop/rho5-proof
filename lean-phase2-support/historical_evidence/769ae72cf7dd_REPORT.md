# D136 报告 — 原论文 V31 小 k 块的真实来源行（阶段 A：READY）

卡片 `parallel/D136/TASK.md`。独占 `Rho5/Shared/XSmallKBranch/**` 与同名聚合。
主回执 `results/X_V31_SOURCE_ROWS_READY.json`；状态 `results/BUILD_STATUS.json`。

## 1. 输入（只读、hash 钉定）

* `rho5_v31_exact/mc_exact_model.json`（82,171 B）sha256
  `5fb91ced098b36174e1f307f543cf30872a075f262d477bc2bdb378b39aa94c5`：
  **22 变量 / 35 共享乘积 / 106 行**，`target=1653/400`，`root_denominator=4800`，`base_multiplier=1600`。
* 同一目录的 `THEOREM.md`（§1 式 (1.1)–(1.3)、§2 符号规范、§3 排序/预算/根盒、§4 106 条共同条件、§5 (5.1) 外包）
  与 `model_source.py`（行的生成源）。只取小模型，**未扫描** 268,817 节点大树。

## 2. 本阶段实际交付（真实编译自审）

| 模块 | exit | wall | 内容 |
|---|---|---|---|
| `Model.lean` | 0 | 3.4 s | 由 JSON **逐项生成**的精确模型数据（变量表、35 乘积对、106 稀疏行、根盒端点、靶值、JSON sha256） |
| `Sound.lean` | 0 | 48.4 s | chart 定义、`IsLift`、`PhysicalBounds`、结构性行引理、McCormick、`RowProp`（106 行 LP 语义）、**104/106 行 soundness**、覆盖核对 |
| `XSmallKBranch.lean` | 0 | 2.2 s | 聚合入口 |
| `XSmallKBranch/Audit.lean` | 0 | 3.0 s | 15 条具名 `#check` + `#print axioms`（真实运行产出） |

守卫：nice10 / `-j1 -M8192` / RSS 8 GiB 看门狗未触发 / AS 12 GiB / 单 Lean / **未用 lake**；0 error、0 panic。

## 3. 已付 vs 未付（精确口径）

**已付 104 行**：

* 95 条物理带行（原 96 条带中 `D₀₀+` 恒零被省略，`2k ≥ 0` 保留）——**全部由 `PhysicalBounds`（式 (1.2)–(1.3)）推出**，不需要任何额外假设；
* `r+w`（由 `|w| ≤ r`）；
* `rAd`、`rBc`、`rAc`（原文 (3.6) 恒等式 + `|D| ≤ k` + 符号规范输入）；
* `B`、`B-A`（原文 (3.1)/(3.2) 恒等式 + `0 ≤ c-d ≤ 1`、`0 < d ≤ 1` + 高值 + `k ≤ 2`）；
* `cd`（原文 (3.3)：`b(c-d) ≥ F/k - 2 ≥ 53/800`）；
* `F`、`plower`——由**显式声明的输入**支付：高值假设 `1653/400 ≤ r - w`；原文 §1.1 的唯一外部低阶输入 ρ₄=4 的实例 `r - w ≤ 4p`。

**未付 2 行（明确列出，未隐藏）**：

| 行 | 索引 | 需要 |
|---|---|---|
| `Fcore`（`F ≤ 9k/4`） | 96 | 原文 §3.1 恒等式 (3.4) 及其各项非负来源（`a,b,c,d∈(0,1]`、`ac,bc,ad ≥ z`） |
| `det3`（`p·k ≤ 4`） | 98 | 原文 §3.2：左上 3×3 行列式 = `p·k` 的完全主元 Schur 身份 + 九条目 ∈ [-1,1] + 3×3 ±1 行列式 ≤ 4 |

**显式声明的输入（不隐藏）**：`HighValue`、`Rho4Input`、`NormalizedSigns`（原文 §2 输出，其论证尚未形式化）、
`SmallThirdPivot`（`k ≤ 2`）。四项都在定理类型中出现。

## 4. 覆盖与外包

* `coverage_complete`（`decide`，内核可复查）：`paidIdx ++ unpaidIdx` 长度 106、去重后仍 106、全部 `< 106`、两组不交；
* `McCormick x y lx ux ly uy` + `mccormick_of_bounds`：原文 (5.1) 四条外包的 soundness；
* `envelope_0 … envelope_34`：35 个共享乘积对根盒端点的逐一实例化；`BoxIn z` 为盒谓词。

## 5. 对应关系（记录，未形式化的部分已标注）

22 变量排列 `(k,r,w,A,B,c,d,p,e,β,u₀,u₁,u₂,x₀,x₁,x₂,v₀,v₁,v₂,q₀,q₁,q₂)` ↔ 原文 (1.1)/(1.3) 的
矩阵条目与 `L/P/S/O` 组合已在 Lean 中显式写出（`Dc/Lc/Pc/Sc/Oc` + `PhysicalBounds`）。
**V43.Physical/实际矩阵 → 该 chart 的识别层尚未形式化**；`F = r - w` 与 `TS.height`/`CanonicalTail.delta`
在 X chart 上的一致性也**仅记录**。这两项是后续阶段（接 D103/D119 已验收资产）的内容。

## 6. 边界

不声称完整 106 行已齐、不声称 §2 符号规范已证、不声称整棵证书树、不声称非原论文符号限制、
不声称全 X 或 `rho = alpha`；未做 LP/数值搜索；未重编上游；未触碰 D135 文件；未写 `outputs/**` 或总队列；
未删除/kill/开服务/联网/写 `/tmp`。

---

# 续：实际矩阵桥与两条矩阵行（READY，2026-09-12 11:38）

按协调者指示，104 行阶段已**封存为部分来源层**（`Model`/`Sound` 未改动、未重编），
在**新叶模块** `MatrixBridge.lean` 中补齐：

* **定义级桥**：`chartState M` 的前 22 个坐标**就是** D119
  `Rho5.Shared.V43MatrixRoundTrip.extractX M`（顺序与 `Model.varNames` 完全一致），
  后 35 个坐标是真实共享乘积；`chartState_isLift`、逐坐标读数（`kk/rr/ww/pp/AA/BB/cc/dd/ee/be/u*/x*/v*/q*`）
  **全部 `rfl`** —— 桥不是假设。
* **同一 height 读数**：`delta_eq_wX_sub_rX`、`ts_delta_eq_wX_sub_rX`（用 `SatFrame` 的 `s = t = r`）、
  `height_reading`（`TS.height M = rr z - ww z`，`w ≤ r` 时）、`abs_delta_eq_F`。
* **两条此前未付的行，用已编译上游定理支付**（不重做 3×3 行列式或 (3.4) 数学）：
  * `det3`（`p·k ≤ 4`，索引 98）← D54 `Rho5.MinorThreeBound.p_mul_k_le_four`；
  * `Fcore`（`F ≤ 9k/4`，索引 96）← D87 `Rho5.LastThreePivotEnvelope.delta_abs_le_nine_quarters_mul_k`
    （`PolyCP` 由 `SatFrame` 经 `Rho5.MinorCPDomain.polyCP_iff_frame` 给出）。
* **封口**：`all_rows_sound_of_satFrame` —— 对实际 `SatFrame M`，在显式输入
  （`PhysicalBounds`/`NormalizedSigns`/`HighValue`/`Rho4Input`/`SmallThirdPivot`）之下，
  **106/106 行**成立（104 冻结行 + 96/98 两行）。
* 编译：`MatrixBridge` exit 0（5.9 s）、`MatrixBridgeAudit` exit 0（3.1 s）、聚合与旧 Audit 重编 exit 0；
  审计 10 条具名目标全部只依赖标准三公理，0 error、0 panic。

**仍未支付（不隐藏）**：96 条物理带的 `SatFrame M → PhysicalBounds (chartState M)` 逐带识别、
原文 §2 符号规范、`F ≤ 4p`（**D138 独占实施**）。阶段 B 待 D135 样本 Lean 通过。

---

# 续二：物理带桥（15 字段）与无 `PhysicalBounds` 前提的 106 行入口（READY，2026-09-12 11:56）

新叶 `PhysicalBridge.lean`（exit 0，3.9 s；审计 exit 0，3.0 s）：

* **`physicalBounds_chartState : SatFrame M → PhysicalBounds (chartState M)`** —— 15 个字段全部由
  **D119 已编译读数**与 `SatFrame` 字段支付：
  `e/β/head` ← `eX/betaX/head_abs_le_one`；`u/x/v/q` ← `uX/xX/vX_abs_le_one`、`qX_abs_le_p`；
  `L/P` ← `LX/PX_abs_le_one`；`D/S/O` ← `DX_le_kX`+`neg_kX_le_DX`、`SX_le_pX`+`neg_pX_le_SX`、`OX_le_one`+`neg_one_le_OX`；
  `k/r > 0` ← `SatFrame.hk/hr`；`|w| ≤ r` ← `SatFrame.cp4 1 1`（尾块完整主元）+ `abs_of_pos`。
* 定义级黏合：`Dc/Sc/Oc (chartState M) = DX/SX/OX M` 三条引理 + 14 条读数引理（全部 `rfl`/`ring` 级）。
* **`all_rows_sound_of_satFrame_noPhys`** —— 实际矩阵 106 行入口，**不再带 `PhysicalBounds` 前提**：
  `SatFrame M → NormalizedSigns → HighValue → Rho4Input → SmallThirdPivot → ∀ i ∈ paidIdx ∪ {96,98}, RowProp i (chartState M)`。
* 冻结不变：`Model`/`Sound`/104 行来源层**未改动、未重编、未重审**；D119/D54/D87 只读复用。
* 审计：5 条具名目标全部只依赖标准三公理，0 error、0 panic。

**仍显式保留**：`NormalizedSigns`（§2，后续支付）、`HighValue`（分支假设）、
`Rho4Input`（`F ≤ 4p`，**D138 独占**，本卡不重复证明）、`SmallThirdPivot`（`k ≤ 2`）。
阶段 B（首真实终端）仍待 D135 样本 Lean 通过；本项不依赖它。

---

# 续三：D138 薄适配与 §3.4 根盒（READY，2026-09-12 12:10）

**(1) `NoRho4.lean`（exit 0，3.3 s；审计 exit 0，3.0 s）**——消费 D138 已冻结的
`Rho5.Shared.SchurFourPivotBound.height_le_four_mul_p`：

* `leadingInput_of_satFrame_high : SatFrame M → HighValue → TS.LeadingInput M`（`delta_ne` 由 `F > 0`）；
* `rho4Input_chartState : SatFrame M → HighValue → Rho4Input (chartState M)`（`F ≤ 4p`）；
* **`all_rows_sound_of_satFrame_noRho4`**：实际矩阵 **106 行**入口，前提只剩
  `SatFrame` + `NormalizedSigns` + `HighValue` + `SmallThirdPivot`（**无 `PhysicalBounds`、无 `Rho4Input`**）。

**(2) `RootBox.lean`（exit 0，7.9 s；审计 exit 0，4.1 s）**——原文 §3.4 的 22 维根盒：

* `PosSigns`（`0 < e`、`0 < β`）与 `0 ≤ u₀` 为**显式输入**；
* `rootBox_chartState : SatFrame M → PhysicalBounds → NormalizedSigns → PosSigns → 0 ≤ u₀ → HighValue → k ≤ 2 → Rho4Input → BoxIn (chartState M)`
  —— `BoxIn` 是**结论**，本叶**不假设根盒**；
* 另有 `rootBox_chartState_noRho4`（去掉 `Rho4Input`，内部走 D138 薄适配）；
* 每个端点都有具名引理（`k_lower`、`r_lower/r_upper`、`w_lower/w_upper`、`A/B_upper`、`c_lower`、`d_lower/d_upper`、
  `p_lower/p_upper`、`e_lower/be_lower`、`q_lower/q_upper` 等），来源见回执 `derivations` 表。

**分工**：通用二叉闭盒覆盖/有限树健全性与 V31 首 C 之前的真实 S 前缀实例由 **M01**
（`Rho5.Shared.MainlineTreeCover`，主线已认领）负责；本卡不重复通用树/前缀证明，
只提供真实矩阵行与 22 维根盒供其消费。首终端仍待 D135 样本 Lean 通过 + M01 覆盖层。

---

# 续四：来源系统打包与 D135 实数门槛更正（READY，2026-09-12 12:22）

**`SourceSystem.lean`（exit 0，4.1 s；审计 exit 0）** 把真实矩阵侧的全部来源事实打包为单一对象
`SourceSystem M`，供 M01 覆盖层/后续检查器消费：

* `rows`：106 条源行 LP 语义（104 冻结 + `Fcore`/`det3` 两条矩阵行）；
* `boxIn`：§3.4 的 22 维根盒（**结论**，由 `rootBox_chartState_noRho4` 导出）；
* `lift`：35 个共享乘积 = 真实乘积；
* `envelopes`：`envelopes_all_chartState` —— 35 个乘积 × 4 条 McCormick 外包。

显式前提：`SatFrame`、`NormalizedSigns`、`PosSigns`（`e>0, β>0`）、`0 ≤ u₀`、`HighValue`、`k ≤ 2`；
`PhysicalBounds`（D119 读数）与 `Rho4Input`（D138）已在前面各叶内部支付。

## D135 证书消费门槛更正（记录在案）

协调者更正：D135 当前 `Linear.Feasible`/`Rational.Feasible` 是 **κ→ℚ（只有理域）**；
已通过的 `v31_check`/`b16_check` 精确计算**有效**，但 `terminal_empty` **不能**直接当作
实际 **ℝ** 来源为空。因此：

* 阶段 B（首终端）**暂停消费**，等待 D135 发布 `CERTIFICATE_RULES_REAL_SOUNDNESS_READY`；
* 本卡**不**重写 D135 检查器、**不**重算其样本、**不**用有理逼近替代缺失的全实数证明；
* 首终端组装路径不变：`SourceSystem`（本回执）→ M01 的 S 前缀覆盖层 → 首 C 盒 → D135 的**实数**无解接口。

---

# 续五：首 C 终端的实数映射（READY，2026-09-12 13:07）

**M01 已消费**（`outputs/assembly_intake_20260912/M01`）：七个 S 分裂轴 `[21,20,19,15,13,14,11]`（中点 0）、
首叶路径 `0000000` 的盒端点、8 个前沿路径，以及 `restricted_source_cover` 的 source∩leaf 接口
（本卡 `SourceSystem` 即其 `source` 端）。**未重复** M01 的通用树/前缀证明。

**`FirstCMap.lean`（exit 0，4.9 s；审计 exit 0）**——首 C 终端的独立精确映射：

* 终端记录（原树第 8 行）：`C 17` + 17 组 `(行号,权重)`；支持行 `[21,24,51,63,90,95,100,103,155,162,163,174,175,221,222,240,242]`
  （8 条源行 + 9 条外包行），权重单位 `1e-6`、**非负已证**（`firstC_w_nonneg`）；
* 显式行系数/右端 `firstC_a/firstC_b`（前 8 条逐项抄自 `mc_exact_model.json`，后 9 条按
  `106+4p+q` 用 (5.1) 从 `productPairs` 与根盒端点生成）；
* 盒 `firstC_L/firstC_U`：22 个变量取 M01 首叶盒端点，35 个乘积取四端点乘积的最小/最大值；
* **`firstC_real_empty`**：任意 `z : Fin 57 → ℝ`，满足 17 条支持行 + 盒内 + 组合残差 `< 0` ⇒ `False`，
  由已编译**实数**核 `Rho5.Certificate.c_contradiction` 给出。

**连接点**：残差 `hneg : (Σ w·b) − Σ min(C·L, C·U) < 0` 正是 D135 精确检查器的输出；
待 `CERTIFICATE_RULES_REAL_SOUNDNESS_READY` 把其 ℚ 计算实数化后即闭合首 C 的 ℝ 空。
本卡不重写检查器、不重算残差、不用有理逼近替代全实数证明。

**保留责任**：M01 的 7 个右兄弟前沿（`0000001/000001/00001/0001/001/01/1`）在本卡；本叶只覆盖首叶 `0000000`；
M02 负责后续完整兄弟子树。

---

# 续六：声明系统 → D135 样本系统的精确对应与实数提升运输（READY，2026-09-12 13:18）

**`FirstCTransport.lean`（exit 0，13.2 s；审计 exit 0，7 条目标）**

1. **精确逐行/逐坐标对应**（4 条整数恒等式，`decide` 内核校验；另有 Python 精确核验全表）：
   * 缩放：变量坐标 `UNIT = 4800·2^128`、乘积坐标 `UNIT²`；
   * 行：`4800·v31System.rows j i = rowScaleZ j·(i<22 ? UNIT : 1)·myCoeffZ j i`
     （`rowScaleZ = 1600` 为 8 条源行、`1` 为 9 条外包行）；
   * 右端：`4800²·v31System.rhs j = rowScaleZ j·UNIT²·myRhsZ j`；
   * 盒：`(i<22 ? 4800 : 4800²)·v31System.lo/hi i = (i<22 ? UNIT : UNIT²)·myLoZ/myHiZ i`；
   * 权重：`v31Weights_eq` 与树中 17 个权重逐项相同。
2. **实数提升点运输**：`feasibleR_v31_of_declared : 盒内 + 17 行 ⇒ FeasibleR Samples.v31System (liftR s)`。
3. **`hneg` 消除**：`no_real_declared : 盒内 + 17 行 ⇒ False`，直接消费 D135 已编译的
   `Samples.v31_terminal_empty_real`（其 `RealTerminals.olean` 哈希与发布回执一致）——
   **不再需要正权组合残差前提**，也未重算 D135 的大 check、未重写其检查器。

**剩余最后一步（未发布实际来源排除）**：证明实际来源点 `s = chartState` 满足首叶盒与 17 条行：
盒 = 根盒（`SourceSystem.boxIn`）+ M01 的 7 个左半分裂条件；8 条源行由 `SourceSystem.rows` 逐项对应；
9 条外包行由叶盒内的 `mccormick_of_bounds` 给出。完成后才发布实际来源排除。

**保留**：M01 的 7 个右兄弟（`0000001/000001/00001/0001/001/01/1`）；M02 负责后续兄弟子树。

---

# 续七：首 C 实际来源连接（**进行中**，2012-09-12 13:49；未发布来源排除）

按协调者要求直接实施三步来源责任。本轮回合完成：

* **35 个乘积坐标的区间乘法界**（`FirstCSource.lean`，exit 0，43.8 s，35 条 `prodBound_0…34`）：
  两因子在首叶盒内 ⇒ `min4 ≤ x·y ≤ max4`（四角端点），逐条 `nlinarith` 真实编译。

**尚未支付（因此未发布来源排除）**：

1. **首叶盒**：根盒 + 真实七左分裂 ⇒ `myLo/myHi`。22 个变量的对照表（叶下端=根下端；七个分裂轴上端 0）已设计；
   57 坐标的装配尝试了三种写法（`fin_cases` 全展开、表格 + `by_cases`、57 显式分支），
   均因 `fin_cases`/`rw` 后的索引形态与 `myLo_lit/myLo_prod` 的匹配问题未通过编译，**已回退回绿**（`FirstCSource` 现仅含 35 条乘积界）。
2. **8 条源行**：`SourceSystem.rows`（`RowProp`）→ `myCoeff/myRhs` 的 LP 形式转换（同一数据两种编码，需要逐行 `Finset.sum` 求值）。
3. **9 条外包行**：叶盒端点 `mccormick_of_bounds` + 真实乘积（结构与 `FirstCMap` 的 9 行一致）。
4. **封口**：`no_real_declared` ⇒ `no_source_left_spine`。

**已确证并保留**：`FirstCTransport` 的精确对应与 `hneg` 消除（续六回执）、`SourceSystem`、`RootBox`、
`FirstCMap`、以及本轮的 35 条乘积界。**未重算** D135 check、**未重算** M01 数据；
M01 的 7 个右兄弟与 M02 的兄弟子树均未触碰。

---

# 续八：索引对齐片段已跑通（2026-09-12 14:05；三项装配仍未完成）

按协调者建议**先做小片段**：`Probe.lean`（exit 0，10.8 s，0 error）现已跑通两处反复失配的索引对齐：

* `leafLoQ/leafHiQ`（22 坐标叶盒端点，ℚ 字面量）+ `myLo_lit/myHi_lit`：`fin_cases i <;> norm_num [myLo, myLoZ, leafLoQ]` ✓；
* `liftAt`：`IsLift` 的 35 分支真实乘积访问器，用 `fin_cases p` 逐分支 `exact hl.lift_<a>_<b>`（`| k => …` 的 match 写法会产生 junk 分支 `⟨35,_⟩` ✗，已避开）。

`FirstCSource.lean` 仍保留 35 条乘积区间界 ✓。**三项装配与 `no_source_left_spine` 仍未完成**，故未发布来源排除。

已记录下一步配方（含实测踩坑）：逐指标系数恒等式要用 `by_cases` + `Fin.ext` + `norm_num`（Fin 字面等式必须 `norm_num`/`decide` 归约，否则 `if` 不降）；求和用 `Finset.sum_add_distrib` + `Finset.sum_ite_eq'`（方向 `if x = a`），避免 `Finset.sum_eq_single`（会在 `⟨0, ⋯⟩` 上留元变量）。

另注：X 上偶发 `failed to create thread`（负载 30+，非确定性），重跑即恢复；本卡所有模块当前 exit 0。

---

# 续九：首 C 实际来源连接完成（READY，2026-09-12 14:22）

**状态：READY** — 回执 `results/X_V31_FIRST_C_SOURCE_READY.json`。
原卡剩余三项 + 封口全部完成并**真实编译**，本叶不再有未付的来源责任。

## 1. 新增模块与真实编译

| 模块 | exit | wall | peak RSS | olean sha256 |
|---|---|---|---|---|
| `Rho5/Shared/XSmallKBranch/FirstCLeaf`（58 定理，1356 行，由 `tools/gen_leaf.py` 生成） | 0 | 44.415 s | 3.13 GiB | `73bc9f70…d33832` |
| `Rho5/Shared/XSmallKBranch/FirstCLeafAudit`（17 目标 `#check` + `#print axioms`） | 0 | 3.086 s | 2.84 GiB | `3b028896…3fa821` |

* 源 sha256：`FirstCLeaf.lean` = `95d4f730…106c840f`，`FirstCLeafAudit.lean` = `e2a3b6f7…9ecbf6b5`（本地与 X 逐位一致）；
* 日志：`logs_x/FirstCLeaf.log`（`e9f5c3ff…`）、`logs_x/FirstCLeafAudit.log`（`aafb1f86…`）；
* 公理：17 目标全部 ∈ {`propext`, `Classical.choice`, `Quot.sound`}（`myCoeffZ_split_0` 仅 `propext`），`sorryAx` 出现 0 次；
* 环境：Lean 4.30.0 / mathlib `c5ea0035…`，绑定含本卡全部祖先（D135 `RealTerminals` olean `3a1248ad…` 与 D135 回执一致），未重编上游。

## 2. 三项来源责任（逐项精确类型见回执与审计日志）

1. **首叶盒（57 坐标）** `leafBox_of_source : BoxIn s → IsLift s → LeftSpine s → ∀ i, myLo i ≤ s i ∧ s i ≤ myHi i`
   * 22 变量坐标：`myLo_lit/myHi_lit`（叶盒字面量表）+ 根盒 `hbox`；七个分裂轴（21/20/19/15/13/14/11）上端由 `hspine` 给 0；
   * 35 乘积坐标：`liftAt`（`IsLift` 35 分支）替换为真实乘积 + `prodBoundAt`（分派 `prodBound_0…34` 的四角区间界）。
2. **8 条实际源行** `srcRow_0…7`：模型行 `RowProp 21/24/51/63/90/95/100/103` ⇒ `∑ myCoeff j i · s i ≤ myRhs j`。
   行系数表由 `myCoeffZ_split_j : ∀ i, myCoeffZ j i = …` 以**整数 `decide`** 内核核验，支撑外为 0 用 `if_neg`（带 Nat 字面量类型标注）消去，和式用 `Finset.sum_insert`/`sum_singleton` 求值。
3. **9 条 McCormick 外包行** `envRow_8…16`：`(p,q)` = (12,1),(14,0),(14,1),(17,0),(17,1),(28,3),(29,0),(33,2),(34,0)，叶端点 `mccormick_of_bounds` 的 ll/uu/ul/lu + `liftAt`；与 D135 `v31RowsL` 第 8..16 行**逐项一致**（本地解析 D135 源码核对系数与右端）。

**封口**：`rows_of_source`（17/17 行）+ `leafBox_of_source` ⇒ 消费已编译 `no_real_declared` ⇒
`no_source_left_spine : SourceSystem M → LeftSpine (chartState M) → False`，
并对实际前提给出 `not_left_spine_of_satFrame`（`SatFrame` + `NormalizedSigns` + `PosSigns` + `0 ≤ u₀` + `HighValue` + `SmallThirdPivot` ⇒ `¬ LeftSpine (chartState M)`）。

## 3. `failed to create thread` 实测诊断（本轮新增证据）

首次两次编译在 ~15.7 s SIGABRT（`lean::exception: failed to create thread`，peak RSS 3.05 GB，未触发 RSS 看门狗/未超时）；
失败日志逐字保留为 `logs_x/FAIL_Probe2_thread_20260912T1407.log`（`32a60967…`）。实测：

* 系统：`ulimit -u` unlimited、`threads-max` 6189743、`max_map_count` 65530、无 cgroup 限制、loadavg 24/27/27；
* 同一源码用 `ulimit -v`=12 GiB 启动 lean 并 0.3 s 采样 `/proc/<pid>/status`：
  **VmPeak = 12481720 KiB（11.90 GiB）对 RLIMIT_AS 12582912 KiB（12 GiB），余量仅 ~99 MiB**，RSS 峰值 3.12 GiB，Threads 峰值 9；
* 结论：SIGABRT 是**线程栈 mmap 撞上地址空间上限**（非确定性、与负载相关），`-M 8192`/`-M 4096` 的 VmPeak 相同；
* 处置：保留失败日志 + 有界重试，**AS 12 GiB / RSS 8 GiB 守卫未改动**；随后 5 次同源编译全部 exit 0。

## 4. 边界（不声称）

* 只闭合 M01 前缀的**第一个左叶**（路径 `0000000`）；7 个右兄弟前沿（`0000001/000001/00001/0001/001/01/1`）
  与其余兄弟子树**未付**，不声称整棵根子树闭合；
* 不声称全部 `0<k≤2`、整个 X 图或 `rho = alpha`；
* 未重算 D135 check/样本、未重写其检查器、未用有理逼近替代全实数证明；未重算 M01 数据；
  Model/Sound/104 行层未改、未重编、未重审。

## 5. 清理记录（不改冻结源）

历史失败探针 `src/Rho5/Shared/XSmallKBranch/Probe2.lean`（sha256 `d0c15cc7…`，其用途已被 `FirstCLeaf` 完全取代）
**移出 src** 至 `tools/probe2_superseded_20260912.lean` 留作证据（不被任何模块 import），构建脚本同步移除 `buildl` 目标；
`src/Rho5/Shared/` 下 22 个模块文件全部 exit 0，无红模块。移动前后逐字节相同（本地与 X 同步移动）。
