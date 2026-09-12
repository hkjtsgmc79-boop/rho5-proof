# 逐步验证 RHO5 证明材料

先选一条验证路线，再下载所需材料。本页提供中文操作入口；各历史计算包的完整入口和迁移限制见[英文完整教程](VERIFY.md)。

## 1. 获取固定版本

```sh
git clone --branch v1.0.0 --depth 1 https://github.com/hkjtsgmc79-boop/rho5-proof.git
cd rho5-proof
git rev-parse HEAD
python3 scripts/fetch.py --list
```

保留输出的提交哈希。Git 仓库包含 Lean、验证器源码、论文和说明；大证书在 Release 附件中。GitHub 自动生成的 “Source code” ZIP 不包含这些大附件。

下载器只使用 Python 标准库，会验证 SHA-256、续传并重组运输分片。下载成功仅说明文件身份正确，尚未执行数学检查。

| 想先验证什么 | 下载与环境 | 能得到什么 |
|---|---|---|
| Lean 解析部分 | 源码包约 6.43 MB；另需 Lean/mathlib 及缓存 | 检查公开的定理及其完整前提 |
| 一个真实精确证书 | 约 18.29 MB，Python 3.10+，不需要 GPU | 检查最后一个具名 54 叶锚点 |
| 完整计算材料 | 全部归档约 4.494 GB；需更大解压空间 | 分别复核组件，并按来源和覆盖关系组合 |

确切文件大小见[下载清单](DOWNLOADS.md)，不能用压缩文件大小估计全部工作磁盘空间。

## 2. 编译第一阶段 Lean

先按 elan 官方说明安装 elan，然后在仓库中执行：

```sh
cd lean
elan toolchain install leanprover/lean4:v4.30.0
lake --version
lake exe cache get
lake build +Rho5.PhaseOne:olean
lake build +Rho5.PhaseOne.Audit:olean
lake build +Rho5.PhaseOne.Examples:olean
lake build +Rho5.PhaseOne.ExamplesAudit:olean
```

保留提交的 `lean-toolchain` 和 `lake-manifest.json`。固定 mathlib 提交为 `c5ea00351c28e24afc9f0f84379aa41082b1188f`。不要通过升级依赖掩盖构建失败。

项目有 646 份规范 Lean 源码，默认入口加载其中 634 个模块。实际常数、达到性和主要解析归约已纳入；第一阶段最终尖锐等式保留两项前提：

```lean
Rho5.PhaseOne.rho5Trace_eq_alpha_of_safety
  (hX : Rho5.Integration.StagedAssembly.XGlobalSafety)
  (hB : Rho5.Shared.BRootCapacityEndpoint.RootEndpointSafety) :
  Rho5.GrowthSupremum.rho5Trace = Rho5.Algebraic.AlphaRoot.alpha
```

编译成功不会消去这两个前提。它们的完整全域支付仍由论文解析论证、外部精确验证和来源覆盖承担，不能把本版本称为完整 Lean 证明。完整类型和公理记录见 [FINAL_THEOREM_TYPES.txt](../lean/FINAL_THEOREM_TYPES.txt) 和 [AXIOMS.json](../lean/AXIOMS.json)。

已有入口与审计的 8.051 秒、例子与审计的 12.021 秒是两次利用上游缓存的运行；不是整项目从零冷编译时间。本次发布没有重新执行完整新机器冷编译。

## 3. 跑一个真实的 54 叶证书

回到仓库根目录。使用 Python 3.10 或更新版本；不要启用 `-O` 或 `PYTHONOPTIMIZE`。

```sh
python3 scripts/fetch.py --group sample
python3 -m zipfile -e downloads/rho5-final-anchor-example.zip replay-output/anchor
cd replay-output/anchor
python3 -S restore_inputs.py
python3 -S verify_joint_anchor.py \
  --v53-dir rho5_v53_exact \
  --b16-dir B_STRUCTURE_16_DELIVERY \
  --output-dir replayed_anchor
```

使用新的解压目录，输出目录 `replayed_anchor` 应当不存在或为空。该例子只需 Python 标准库，历史 X 验证约 184.37 秒；其他机器可能不同。

预期关键结果：

```text
COMPLETE_ANCHOR_ALPHA_SAFE
parent_index = 435003
anchor_path = 10011101
paid_leaves = 54
remaining_sources = []
whole_parent_closed = false
whole_B_closed = false
```

末尾两个 `false` 是正确的范围标注：这个例子支付具名锚点，完整父框和 B 域还需要其他证书。它不重新运行发现这份证书的搜索。

## 4. 继续复核完整计算部分

在仓库根目录按需下载：

```sh
python3 scripts/fetch.py --group x --group upstream
python3 scripts/fetch.py --group b
```

完整材料及其原验证器已一起提供。在线 `verifiers/` 只是便于阅读的逐字节源码镜像；实际运行应从完整归档中进行，保留模型、输入和冻结目录结构。X 各组件的确切入口见[英文教程第 4 节](VERIFY.md#4-check-the-x-domain-components)。

B 历史原根归档有 5 个运输分片，下载器自动还原原始压缩包并核对整体哈希。两份 B 归档的外层解压文件约 21.54 GB，尚未包含嵌套解压和新运行输出。规划完整计算复核可先预留 32 GB RAM、至少 50 GB 工作磁盘，完整 Lean 与计算材料共存可预留 80–100 GB；这些是规划余量，不是实测最低要求。

解压到独立 Linux 工作目录，保留路径。从 `rho5_independent_acceptance_20260911_11` 进入原根检查：

```sh
python3 -B -S runtime/r54_replay.py \
  --tree checkpoint/B17_ROOT.json \
  --out REPLAY_ROOT_NEW.json \
  --workers 8 --backend fraction --allow-open
```

输出文件必须是新的。原根预期为 `PARTIAL_EXACT_COVERAGE_ONLY`，包含 749,693 个节点、374,839 个矛盾终点、4 个 alpha 安全终点和 4 个开放终点。四个旧开放终点由后续完整覆盖分别支付；不要改写旧文件让开放数变成零。

原根历史 8 进程运行约 6.34 小时，之后还需要父框、alpha 覆盖及最终来源组合，不能据此给出整套证明的完成时间保证。

**完整重放的现有限制：** 目前尚没有经过新机器演练的一键全链命令。部分最终组合配置保留历史绝对路径，且组合器使用之前验收的收据。独立复核必须明确迁移路径、保留冻结输入哈希与 435003 父框的 239/240 基线，执行所需数学检查，再组合新收据。不能关闭来源检查，也不能只验旧 PASS 收据的哈希来代替数学重放。详见[英文教程第 5 节](VERIFY.md#5-check-the-b-root-and-final-covers)和[论文补充索引 S7–S8](../paper/RHO5_SUPPLEMENTARY_INDEX.pdf)。

## 5. 如何记录结果

记录版本、提交哈希、资产清单哈希、处理器、软件版本、命令、并行进程数、墙钟时间、峰值内存和磁盘（如有测量）、退出状态及结果范围。把以下四件事分开写：

1. 下载文件并核对身份。
2. Lean 检查声明及其完整前提。
3. 精确验证具名计算证书。
4. 完成全部必要来源与全域覆盖的组合。

本仓库发布的是这些材料及已有运行记录。Python/C++ 验证器尚未经程序级形式验证；完整计算树也没有在 Lean 内核内全部验完。当前采用的正是论文所说明的“Lean 解析形式化 + 可复现精确证书验证”路线。
