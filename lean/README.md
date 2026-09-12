# RHO5 第一阶段 Lean 源码包

本项目提供已验的解析、代数和原矩阵来源归约，以及保留明确前提的最终接口。默认入口是 `import Rho5.PhaseOne`。

无外部安全前提的已证成果包括：实际 α 的精确隔离与唯一根身份；原候选系统的存在及与实际 α 的相容性；达到 α 的真实矩阵和合法路径；`α ≤ rho5Trace ≤ 81/16`；原全局最大者的存在；从超过 α 的原最大者到实际 X 或原 B 根容量端点的强来源归约。D84 还给出真实局部 ODE 轨迹存在和物理资源终点，保留起始区域、严格时间空间预算及物理资源前提。

最终 sharp 等式是**条件定理**：

```lean
Rho5.PhaseOne.rho5Trace_eq_alpha_of_safety
  (hX : Rho5.Integration.StagedAssembly.XGlobalSafety)
  (hB : Rho5.Shared.BRootCapacityEndpoint.RootEndpointSafety) :
  Rho5.GrowthSupremum.rho5Trace = Rho5.Algebraic.AlphaRoot.alpha
```

`hX` 要求完整 Physical X 域上高度不超过实际 α。`hB` 要求原 D142 定义的每个根容量端点高度不超过实际 α。当前源码没有提供这两个全域命题的证明；未来证明还需完成相关来源、语义和完整覆盖接线。局部图、有限样本、外部程序 PASS 或已验的个别子树都不能替代它们。实际 α 的存在与达到性已经证明，不再列为外部责任。

`Rho5.PhaseOne` 只直接导入 C02 修订版 `Conditional` 与 D84 `PhysicalTrip`；33 个便捷名称通过 Lean `export` 指向原声明，原完整类型和证明保持不变。新 `Examples` 和 `Audit` 均不由产品默认入口导入。既有解析依赖中少数原 owner 聚合入口自带历史审计；这些按原闭包保留，不应称为所有层级都没有审计模块。

- [覆盖与定理目录](docs/COVERAGE.md)
- [外部计算及来源覆盖责任](docs/OBLIGATIONS.md)
- [使用示例](docs/USAGE.md)
- [固定环境与构建步骤](docs/BUILDING.md)
- [编译器输出的完整公开类型](FINAL_THEOREM_TYPES.txt)
- [公理回执](AXIOMS.json)
- [源码来源映射](SOURCE_MAP.json)

本包含646份规范Lean源码（35,027,225字节），默认加载634个项目模块；其余12个源码模块可供独立复查。33个产品名称及14个示例定理的实际公理记录均只使用标准公理。

工具链固定为 Lean 4.30.0，mathlib 固定在 `c5ea00351c28e24afc9f0f84379aa41082b1188f`，并附原锁文件。项目构建以包内相对路径进行；溯源证据中的历史机器路径只用于审计。

本次实测是 X 已验缓存上的新产品入口、独立审计及另行记录的使用示例编译；上游证明复用 C02 rebound 与 D84 等正式证据。没有在新机器冷编全库，也没有声称 Mac 对 Linux 对象完成验证。源码包不以历史 X 缓存为重建必需品，第三方依赖仍需依照锁文件取得。

G02/G03 等阶段二树样本已经冻结，仅在责任文档中索引。它们不进入本包默认产品导入，也不是第一阶段交付的前置条件。本次没有启动新的树计算、生成证书或重建上游证明。
