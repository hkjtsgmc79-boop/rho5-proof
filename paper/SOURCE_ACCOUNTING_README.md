# 566 个组成来源与 469 个原父责任的对应表

本文件组回应审稿意见 D 的计数与来源追踪要求。**本次只做原回执只读导出和账项对应核对，没有运行数学冷重放，也没有改动原回执或大树。**

## 两种计数的含义

566 是四个残余父框内部的组成来源数；这些来源共同支付原根的 4 个 O 所代表的 4 个原父责任。再加原记录已付的 465 个原父责任，得到 469。566 与 469 不是同一层级，也不是一一对应。

| 原父 ID | 组成来源数 | 原根中已记录的 O 路径 |
|---:|---:|---|
| 338726 | 111 | `10011000010101010` |
| 435003 | 240 | `10111000001100011000010111011` |
| 563285 | 159 | `1101000101111` |
| 675104 | 56 | `1110101001111` |

**111 + 240 + 159 + 56 = 566；465 + 4 = 469。**

原根路径及闭盒哈希仅保存在 JSON 的 `parents[].actual_original_root_binding` 中；没有将父框内部的 `relative_target_path` 猜接到原根路径。父框内部路径以其冻结基线和来源迁移为背景，须通过原绑定证据解释。

## 如何追踪任意一条

1. 在 `SOURCE_ACCOUNTING_566_TO_469.json` 的 `constituents` 中按 `task_id` 或 `(original_parent_id, relative_target_path)` 查找。
2. 用该项 `source_receipt_file` 和 `source_receipt_sha256` 定位 `final_cover.tar.gz` 中的原始回执；`parents[].source_receipt.local_file` 另给现存本地副本位置。
3. `target_json_pointer` 指向完整原项，`original_open_path_json_pointer` 指向原责任路径；`original_binding_evidence.json_pointer` 指向完整、未经改写的原绑定证据。
4. `excerpt` 保留部分原字段及其嵌套定位。体积控制使用 JSON pointer，未把省略的证据假称已随本 JSON 全量提供。完整回执必须与此索引同时可获得。
5. 再由父级 `actual_original_root_binding` 追踪四个实际原根 O，并核对父回执在最终 overlay 中的哈希引用。

JSON pointer 使用 RFC 6901，并相对于该条的原始回执。原文件 SHA256 按原始字节计算；对象指纹按 UTF-8、键排序、无多余空白、`ensure_ascii=False` 的 JSON 计算。对象指纹用于导出定位，不是数学验收签名。

## 本次确实完成的核对

- 四份原父回执的实际字节 SHA256 与最终 overlay 正式引用逐一相等。
- 每父框条目数分别为 111、240、159、56，合计 566。
- 每父框原责任路径无重复；`targets.target_path` 集合与 `original_open_paths` 集合恰相等。
- 全部 566 个 `(原父 ID, 相对路径)` 与 task_id 均唯一；全部原项 `closed` 字段为 true，父回执记载 open 为 0。
- 父级 ID 恰为最终 overlay 的四个原根 O，原记录计数满足 465 + 4 = 469。
- 导出结束前再次确认四个原回执字节身份未改变。

以上是对原记录内容、身份和集合关系的核对。**没有重新证明每条记录的数学有效性，没有读取或重新遍历大根，也没有在此逐项枚举此前 465 个已付责任。**

## 原始来源

- 最终 overlay：`/Users/mike/Documents/Codex/2026-09-07/rho5-mainline-v2/outputs/paper_20260911/evidence/final_overlay/ROOT_COMPLETE_OVERLAY.json`
- 最终 overlay SHA256：`43dbb784c871ecad4b6ff10047f39a2dad7a69a0b6eb392b40c9a56306e6ea34`
- 父 338726：`/Users/mike/Documents/Codex/2026-09-03/rho5-cqg-cofactor-calibration/outputs/b14_production_20260911/adoption_receipts/deep/parents/338726/ALPHA_COMPOSITE_RESULT.json`
  - SHA256：`12463d6ea5fba04a4ab8562eb74abd9f8c2ab348579223ba1824730165fbebd2`
  - 保存档案内位置：`final_cover.tar.gz/rho5_deep500_all_open_20260910_08/parents/338726/ALPHA_COMPOSITE_RESULT.json`
- 父 435003：`/Users/mike/Documents/Codex/2026-09-03/rho5-cqg-cofactor-calibration/outputs/b16_v53_closure_20260911/final_overlay/PARENT_435003_COMPLETE.json`
  - SHA256：`6451a87db7383915b58bb3174581a4c81c38eca9a8aae32641d00083ad6cacb9`
  - 保存档案内位置：`final_cover.tar.gz/rho5_b16_v53_closure_20260911_18/final_overlay/PARENT_435003_COMPLETE.json`
- 父 563285：`/Users/mike/Documents/Codex/2026-09-03/rho5-cqg-cofactor-calibration/outputs/b14_production_20260911/adoption_receipts/deep/parents/563285/ALPHA_COMPOSITE_RESULT.json`
  - SHA256：`27ec79e257ffe9205d8fecfdee4f06c885cc9d8ee0b052f831931dce41109c17`
  - 保存档案内位置：`final_cover.tar.gz/rho5_deep500_all_open_20260910_08/parents/563285/ALPHA_COMPOSITE_RESULT.json`
- 父 675104：`/Users/mike/Documents/Codex/2026-09-03/rho5-cqg-cofactor-calibration/outputs/b14_production_20260911/adoption_receipts/deep/parents/675104/ALPHA_COMPOSITE_RESULT.json`
  - SHA256：`f3236f455b4a7824a3dabe508a732f0d174b9ecf276a7835cbb05250d30be42b`
  - 保存档案内位置：`final_cover.tar.gz/rho5_deep500_all_open_20260910_08/parents/675104/ALPHA_COMPOSITE_RESULT.json`

## 仍需独立数学复核的范围

本对应表不替代原始证书负载、递归数学依赖、来源迁移验证、α 安全证明或整根 Fraction 验收。它也没有补成可迁移的全链冷重放驱动。独立审稿应继续按 `REPRODUCIBILITY.md` 与公开验证指南的作用域执行相应数学接受器。

本 JSON：991,977 字节；SHA256 `1a5dd9f14d165cd26496a6134b458e90ef65d4353363a7da0ca819f2fda2bc62`。
