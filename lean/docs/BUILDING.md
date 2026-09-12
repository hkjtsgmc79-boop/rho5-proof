# 从固定依赖构建

解压 `SOURCE.zip`，进入 `rho5-phase-one` 目录。包内已有完整项目，无需另建 Lake 项目。项目的构建配置和源码不使用历史 X 或个人目录。

固定环境：Lean `leanprover/lean4:v4.30.0`（commit `d024af099ca4bf2c86f649261ebf59565dc8c622`）；mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`。原 `lake-manifest.json` 的 SHA256 为 `6fa600a652ca1ef77814e08127d1078febb38e3018ed9f8b1c5683b92427b789`。manifest 中第三方包的精确 `rev` 已固定，部分历史 `inputRev` 写 main 并不把锁定提交改成浮动版本。

在已安装 elan 且可取得固定依赖的环境中：

```sh
cd rho5-phase-one
elan toolchain install leanprover/lean4:v4.30.0
lake --version
lake exe cache get
lake build +Rho5.PhaseOne:olean
```

`lake exe cache get` 用于取得固定 mathlib 的预编译缓存及其依赖；需要网络和磁盘。如果缓存不可用，应按该固定版本的依赖构建流程取得第三方对象，不能把锁文件升级到新版来代替。包内不附 mathlib、Lean运行时或历史 `.lake` 缓存。这里没有执行新机器依赖获取或冷构建。

默认 `lake build` 也仅选择产品入口及其依赖。配置保留 `roots = ["Rho5"]` 以识别所有项目内导入，同时用 `globs = ["Rho5.PhaseOne"]` 限定默认库目标。它不会自动编译附带的审计和示例，也不会选择阶段二树实例。该语义核对了固定 Lake 的 `LeanLibConfig` 定义与命令帮助；本次没有运行 Lake 全项目构建。

按需构建独立审计或例子：

```sh
lake build +Rho5.PhaseOne.Audit:olean
lake build +Rho5.PhaseOne.Examples:olean
lake build +Rho5.PhaseOne.ExamplesAudit:olean
```

本包有646份规范 Lean 源码，共35,027,225字节（约33.4 MiB）；默认产品实际加载634个项目模块。它们包括已验 α/G04 和局部解析证明所需的有限精确数据。225,469字节只是旧C02薄层镜像字段，不能当作完整源码闭包的体积。

本次真实编译记录：P01产品与审计合计8.0513596534729秒；D161示例与审计合计12.021秒，均在X已有缓存上完成。两路四模块时长之和20.0723596534729秒不是同一次冷构建或总历时。上游 C02 rebound 和 D84 等证明直接继承正式编译证据，没有重新编译。Mac及新机器全库冷构建未验证。

P01使用规范 C02 Rho5 对象和 D84 已验 ODE Mathlib 缓存视图。每次调用保留9项有限基础指纹及直接自有依赖的前后快照；另核对新增138个上游模块的现行源和对象指纹。134个旧LocalAnalysis模块没有因此获得新的历史逐模块编译时源绑定。这项限制随 [构建状态](../BUILD_STATUS.json) 与 [源码映射](../SOURCE_MAP.json) 一并保留。

历史机器路径、原始运行器和回执都在 `evidence/` 中，仅用于溯源，不是上述重建步骤的路径依赖。
