# D160 可迁移项目源码材料（边界说明）

本目录是第一阶段非大规模计算总装的**项目源码闭包**，由 D160 归集；产品入口、README/coverage 主体、Examples
分别由总装 Codex、D158/D159、D161 负责，本包不重复。

## 内容

| 路径 | 内容 |
|---|---|
| `project/Rho5/**` | 642 个模块，每个一个规范版本。**默认来源集 633** = C02 `Conditional` 闭包 495 + P01 真实新增上游 138（+ 产品模块 `Rho5.PhaseOne`，由总装 Codex 写 ⇒ 默认合计 **634** = P01 `loaded_Rho5`）。另 9 个非默认：D84 lane 伞/审计 4、C02 三行聚合 1、C02 审计 4（`default_set=false`） |
| `project/lean-toolchain` | `leanprover/lean4:v4.30.0`（原样） |
| `project/lakefile.toml` | `lean_lib Rho5` + mathlib pin `c5ea00351c28e24afc9f0f84379aa41082b1188f`（原样，未升级） |
| `project/lake-manifest.json` | 原锁；sha256 `6fa600a652ca1ef77814e08127d1078febb38e3018ed9f8b1c5683b92427b789` 与 C02 最终 binding 记录一致 |
| `SOURCE_MAP.json` | 模块 → 源路径/项目相对路径/源哈希/对象哈希/证据出处/候选与冲突解决 |
| `SOURCES_READY.json` | 计数、复制哈希核验、未解决冲突、D84 增量、固定环境、复用 vs 新增、边界 |
| `RELEASE_READY.json` | 交付状态与完成度对照（含唯一缺项说明） |
| `SELF_REVIEW.md` | 逐条自审 + 诚实限定 |
| `SHA256SUMS` | 全包逐文件哈希（相对包根） |
| `logs/`, `evidence/` | 归集与复核日志、binding/D84/D39-D120/锁文件证据、`VERIFY.json` |

## 交付根

`work/dsh-main/parallel/D160/deliverable/`（卡面输出位置已更正；协调者负责最终搬运）。自审回执：`SELF_REVIEW_RECEIPT.json`。

## 默认入口与边界

- 默认来源集：`default_set=true` 的 633 个模块（495 + 138）；产品默认入口：`import Rho5.Integration.StagedAssembly.Conditional`（原 C02 条件终点）。
  `Rho5.Integration.StagedAssembly`（三行聚合）与 4 个 `*Audit` 文件仅供复查，**不进**默认 import。
- 默认 Lake roots 将由总装 Codex 写的 `Rho5.Phase1`（卡面写作 `Rho5.PhaseOne`）承担；本包**不创建**该模块。
- D84 的 `Mathlib.Analysis.ODE.PicardLindelof` 属于第三方缓存职责（D84 门），不在本包内，也不在 Mac 冷编。
- 本包不包含：`.lake` 缓存、mathlib/Lean runtime、第三方包、具体树/检查器实例、任何新证书。
- 两项全域安全前提（`XGlobalSafety`、原 D142 `RootEndpointSafety`）仍为**显式未付条件**；本包与 README/coverage
  不得把它们写成已成立。
