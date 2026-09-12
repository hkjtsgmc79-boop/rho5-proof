# RHO5：论文、Lean 解析形式化与精确计算证书

**马千里、吴超** · 浙江大学；马千里另属 WUJIE AI  
联系：qianli.ma@zju.edu.cn

本仓库随论文公开实五阶完全主元消元增长因子问题的证明材料：论文解析论证、第一阶段 Lean 源码、精确证书及 Python/C++ 验证器。

## 从哪里开始

| 入口 | 内容 |
|---|---|
| [逐步验证教程](docs/VERIFY.md) | 固定版本、Lean 构建、小证书和完整计算路线 |
| [大小与计算资源](docs/DOWNLOADS.md) | 下载量、解压空间、已有耗时及未测量事项 |
| [证明范围对应表](docs/PROOF_MAP.md) | Lean 已证明什么，哪些责任仍由外部计算和书面论证承担 |
| [论文](paper/rho5_manuscript.pdf) | 主论证 |
| [补充索引](paper/RHO5_SUPPLEMENTARY_INDEX.pdf) | S1–S8 对应材料和真实验证入口 |
| [第一阶段 Lean 中文说明](lean/README.md) | 组装范围、精确类型和原始构建说明 |
| [固定版本下载](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/tag/v1.0.0) | 大证书附件与原源码包 |

Lean 包只有约 **6.43 MB**；可以先看已形式化的解析部分。约 **18.3 MB** 的最后 54 叶轻包适合体验真实精确验证。完整证书规模为 GB 级，可以按需下载。

```sh
python3 scripts/fetch.py --list
python3 scripts/fetch.py --group sample
```

脚本自动下载、续传、核对哈希，并重组大归档的运输分片。它不执行数学验证。GitHub 自动生成的 “Source code” ZIP 不包含另外附加的大证书。

## 当前准确范围

第一阶段组装包含646份规范 Lean 源码，默认加载634个模块。实际 alpha、达到性、主要解析归约和局部轨迹已有形式化成果；新入口、审计和例子有缓存编译成功记录。

最终等式保留 `XGlobalSafety` 和原 `RootEndpointSafety` 两项全域安全前提。现阶段不宣称完整全域证书已经在 Lean 内核内验完，也不宣称 Python/C++ 验证器经过程序级形式验证。

证书检查不需要重新运行发现证明的搜索。完整计算复核仍须执行必要组件的数学检查并接回完整来源覆盖；只验文件哈希或旧 PASS 日志不等于重新证明。部分最终组合配置仍需保留输入身份的路径迁移，尚没有经过新机器演练的一键全链重放。

本次先公开 GitHub；Zenodo 归档和 DOI 后续补充，不提前声称已经完成。
