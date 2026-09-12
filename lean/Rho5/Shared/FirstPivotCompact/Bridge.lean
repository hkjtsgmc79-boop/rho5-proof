/-
D26 — 与 D23 域的桥接、以及**精确未付接口**清单
=================================================

**桥接.** D23 的首主元增长值集合 `Rho5.FirstPivotDomain.FirstPivotGrowthValues` 的矩阵
条件与本卡的 `K` 逐字相同，因此

  `g ∈ FirstPivotGrowthValues ↔ ∃ A ∈ K, ∃ values, LegalTrace A values ∧ g = growthRatio A values`

（`mem_firstPivotGrowthValues_iff_exists_mem_firstPivotDomain`）。这把“未来在 `K` 上做
达到性”与“真实增长值集合”接上：任何在 `K` 上取到最大值的连续泛函结论，都可以作用到
D23 的集合成员所对应的矩阵上。

**达到性接口（只到这里）.** `isCompact_firstPivotDomain` + `firstPivotDomain_nonempty`
给出 Weierstrass 形式：**任何**在 `K` 上连续的实泛函取到最大值
（`exists_isMaxOn_of_continuousOn`）。本卡只把它作为**工具**交付，**不**对增长泛函使用它
——见下面的未付接口。

## 未付接口（后继卡的精确清单）

1. **变长轨迹**：`Rho5.CompletePivotPath.LegalTrace` 是归纳关系，轨迹长度随矩阵变化
   （0–5 项），且 ties 允许不同选择；因此不存在“`A ↦ values`”的连续映射，
   `K` 紧不能直接对轨迹空间使用。
2. **后续小主元与零终止**：第二步起需要对 `pivotSchur A 0 0` 的某个条目（或 `(0,0)`）
   非零——这是**离散**条件（argmax 选择）；为零时轨迹提前以 `zeroStop` 结束
   （D13 的 `zeroStop` 分支）。`K` 被分成有限多个“分支定义域”，每个分支带自己的
   非零/位次条件，本卡未证明这些分支的相对闭/开性或它们的并覆盖。
3. **峰值连续性**：D17 的 `tracePeak` 对**列表**连续（`max` 的有限折叠），但列表不是
   `A` 的连续函数（见第 1 条）；因此 `A ↦ tracePeak (轨迹 A)` 的连续性未支付。
4. **上确界达到**：`rho5Trace := sSup GrowthValues` 的达到性（以及 D18 的非空/有界支付）
   不在本卡；本卡只提供“连续泛函在 `K` 上取到最大值”的必要工具。
5. **第一步之后的紧性**：`pivotSchur A 0 0` 的像集是否有界/闭（其定义域上的连续性已给出，
   但像是 4×4 矩阵域，需要另一次约化）未在本卡支付。

以上都在报告中记为明确未付条件；本卡**不**从 `K` 紧跳到“最优达到”。
-/
import Rho5.Shared.FirstPivotCompact.Schur
import Rho5.Shared.FirstPivotDomain

namespace Rho5.FirstPivotCompact

open Rho5

/-- **桥接（卡目标 1/4 的接口）**：D23 的首主元增长值集合就是“`K` 中矩阵的真实合法轨迹
增长比”的集合。两个定义的条件逐字相同，故两向都是直接拆装。 -/
theorem mem_firstPivotGrowthValues_iff_exists_mem_firstPivotDomain {g : ℝ} :
    g ∈ Rho5.FirstPivotDomain.FirstPivotGrowthValues ↔
      ∃ A ∈ firstPivotDomain, ∃ values : List ℝ,
        Rho5.CompletePivotPath.LegalTrace A values ∧
          g = Rho5.GrowthModel.growthRatio A values := by
  constructor
  · rintro ⟨A, values, hmax, h00, hpiv, htrace, rfl⟩
    exact ⟨A, ⟨hmax, h00, hpiv⟩, values, htrace, rfl⟩
  · rintro ⟨A, hA, values, htrace, rfl⟩
    obtain ⟨hmax, h00, hpiv⟩ := hA
    exact ⟨A, values, hmax, h00, hpiv, htrace, rfl⟩

/-- **达到性工具（Weierstrass 形式）**：`K` 非空且紧，故 `K` 上任何连续实泛函取到最大值。

这是后继“达到性证据”的接口；本卡**不**对增长泛函断言它连续（未付接口 1–3）。 -/
theorem exists_isMaxOn_of_continuousOn {f : Matrix5 → ℝ}
    (hf : ContinuousOn f firstPivotDomain) :
    ∃ A ∈ firstPivotDomain, IsMaxOn f firstPivotDomain A :=
  isCompact_firstPivotDomain.exists_isMaxOn firstPivotDomain_nonempty hf

end Rho5.FirstPivotCompact
