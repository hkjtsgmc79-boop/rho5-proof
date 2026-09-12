# BUILDING — 第一阶段已验总装的可迁移构建说明（D161）

本文件说明如何在一个**新机器**上从源码构建 `Rho5.PhaseOne.Examples`（以及它依赖的 C02 总装入口）。
它明确区分三件事：

1. **固定环境**（Lean / mathlib / 依赖 pin）；
2. **本次在 X 上实测的增量编译**（复用已有 C02 对象根与第三方缓存）；
3. **尚未做的 fresh-machine 完整冷构建**（本项目**没有**在干净机器上从零构建过整条源码闭包，
   也**没有**在 Mac 上编译过任何 Lean 目标）。

---

## 1. 固定环境（必须逐位相同）

| 项 | 值 | 来源 |
|---|---|---|
| Lean | `4.30.0`，`x86_64-unknown-linux-gnu`，commit `d024af099ca4bf2c86f649261ebf59565dc8c622` | X 实测 `lean --version`；C02 绑定文件同值 |
| mathlib | commit `c5ea00351c28e24afc9f0f84379aa41082b1188f` | C02 `IMPORT_SOURCE_OLEAN_BINDING.json` 的 `mathlib_revision` |
| lake manifest | SHA256 `6fa600a652ca1ef77814e08127d1078febb38e3018ed9f8b1c5683b92427b789` | 本卡在 X 上对 `rho5_lean_pilot_20260911/project/lake-manifest.json` 独立复核，与文档记录一致 |
| 第三方包 | `batteries`、`Qq`、`aesop`、`proofwidgets`、`importGraph`、`LeanSearchClient`、`plausible`（由上面 manifest 锁定） | C02 `tools/build.py` 的成功记录 |
| Lean 二进制 | pilot runtime：`rho5_lean_pilot_20260911/runtime/lean-4.30.0-linux/bin/lean` | C02 同一路径 |

**不要升级、不要用浮动最新版、不要换内核。**

## 2. 源码与对象的获取

* 项目源码：按 C02 最终绑定 `IMPORT_SOURCE_OLEAN_BINDING.json` 的 `source_closure`
  （**495** 个项目模块）收包，每模块一个规范版本；该闭包的镜像源码字节数记录为
  `mirror_source_bytes = 225469`（约 220 KB），因此**可迁移源码包很小**，
  不需要搬运 `.lake/`、历史任务目录或日志。
* 源码冲突：按最终 source/olean 绑定解决（不要按目录时间或"先找到哪个用哪个"）；
  13 个 JetBounds 修订模块绑定 D39 源，其余按最终 manifest。
* 本项目**产品源码**（本卡新增）只有两个文件：
  `src/Rho5/PhaseOne/Examples.lean`、`src/Rho5/PhaseOne/ExamplesAudit.lean`。

## 3. 推荐构建步骤（新机器）

```bash
# 1) 取得固定工具链（elan 示例；任何等价方式都可以，只要 commit 一致）
git clone https://github.com/leanprover/lean4 lean4 && cd lean4
git checkout d024af099ca4bf2c86f649261ebf59565dc8c622

# 2) 建 lake 包并锁定 mathlib 到 pin
lake +leanprover/lean4:d024af0 new rho5phase1 && cd rho5phase1
#   把 lakefile.lean / lake-manifest.json 换成随包交付的原锁文件（不要 lake update）

# 3) 取 mathlib 预编译缓存（否则要自己构建 mathlib：数小时级，未在本项目验证）
lake exe cache get          # 若该 commit 无缓存，则必须 lake build Mathlib（很慢）

# 4) 放入项目源码（495 个模块 + 本卡两个文件）
cp -r /path/to/rho5_src/Rho5 .

# 5) 只构建产品入口（不要 build 全库、不要自动发现所有 Rho5 模块）
lake build Rho5.PhaseOne.Examples
#   或不经 lake、用同一守卫直接调 Lean：
#   LEAN_PATH="<本包build>:<mathlib build>:<第三方包 build>" \
#     lean -j1 -M8192 -R src -o build/lib/lean/Rho5/PhaseOne/Examples.olean \
#          src/Rho5/PhaseOne/Examples.lean
```

注意：

* 默认构建目标只有产品入口；**不要**把整个 `Rho5.Integration.*` 或全部历史任务模块自动发现为默认目标
  （那会拉入与第一阶段无关的实例）。
* `Rho5.PhaseOne.ExamplesAudit` 是独立审计文件，**不要**让产品默认 import 它。
* 若使用 lake，`lean_lib` 的 globs 应显式列出产品入口，而不是 `Rho5.*`。

## 4. X 上本次实测的是什么（增量，不是冷构建）

在已有 **C02 修订对象根** `/root/microscope_ws/rho5_codex_c02_assembly_20260912/rebuild_01/build`
（930 个 Rho5 olean，符号链接进本卡 `build/lib/lean`，**未重编**）+ 第三方缓存
（`D141/cache/lean` 的 mathlib + pilot 的 7 个包）之上，只编译了本卡两个模块：

| 模块 | exit | wall | 子进程峰值 RSS | olean sha256（前 16 位） |
|---|---:|---:|---:|---|
| `Rho5.PhaseOne.Examples` | 0 | 6.011 s | 4.26 GB | `2e9619f76eca553f` |
| `Rho5.PhaseOne.ExamplesAudit` | 0 | 6.010 s | 1.74 GB | `74280f632cdfc69b` |

即：**实测的是"已有缓存 + 两个新模块"的增量**，guard 为 `nice 10`、`-j1 -M8192`、
RSS 8 GiB 看门狗（未触发）、AS 12 GiB；编译前检查 `MemAvailable ≥ 16 GiB`、磁盘 `≥ 10 GiB`。

## 5. 没有做、也不能声称的（fresh-machine 状态）

| 项 | 状态 |
|---|---|
| 干净机器上从零构建整条 495 模块源码闭包 | **未做**（本项目没有该测量） |
| 干净机器上构建 mathlib（无 cache 情形） | **未做**（数小时级，需自备算力） |
| Mac / 任何非 X 平台编译本项目 | **未做**；本阶段所有 Lean 运行都在 X 上 |
| C02 对象的重建 | **未重编**；直接复用已接收的修订对象根（源哈希与对象哈希见 `RELEASE_READY.json`） |
| 全库冷编 / 全树重跑 | **未做**，且不属于第一阶段 |

因此：`BUILDING` 给的是**正常用户步骤 + 依赖获取需求**；把"X 上增量成功"等同于
"新机器冷构建已验证"是不成立的，本文档不作此声称。

## 6. 复现本卡结论的最小检查

```bash
# 只检查公开类型与公理（应看到 hX/hB 仍显式，且只用标准三公理）
lake build Rho5.PhaseOne.ExamplesAudit     # 或直接 lean 调用审计文件
# 输出应在 RHO5_PhaseOne_ExamplesAudit 的日志里：13 条 #check + 12 条 #print axioms，
# 无 sorryAx。
```
