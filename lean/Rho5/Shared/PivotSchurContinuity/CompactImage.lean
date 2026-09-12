/-
D32 — 单步 Schur 像的紧性适配与**未付接口**
=============================================

**卡目标 4.** 只做这一条新的单步接口：把“给定条目有界闭盒 ∩ `CPDomain p q`”的紧性
（`CPDomain.lean` 的 `isCompact_entryBox_inter_CPDomain`）与
`ContinuousOn (pivotSchur · p q) (CPDomain p q)`（目标 3）合起来，得到 Schur 像的紧性：

* `isCompact_image_pivotSchur`：任何 `K ⊆ CPDomain p q` 且 `K` 紧，则
  `pivotSchur · p q '' K` 紧（`IsCompact.image_of_continuousOn`）；
* `isCompact_image_pivotSchur_entryBox_inter`：对给定的条目上下界 `lo hi`，
  盒子交域的 Schur 像紧。

**不复制 D26 的第一步多项式连续性**：D26 处理的是首主元 `(0,0)`、`A 0 0 = 1` 的域上
“除以 1 后退化为多项式”的连续性；本卡处理的是一般 `(p, q)` 且**允许主元为零**的
合法主元域，零点用条目估计挤压，非零点用连续除法——两者是不同的数学内容，本卡不重证
D26 的多项式结论，也不引用它。

## 未付接口（本卡不宣称 rho5 达到）

1. **全路径的有限分支/零填充表示**：`LegalTrace` 是归纳关系（长度 0–`n+1`、ties 可选、
   中途可 `zeroStop`）。要把“路径上的 Schur 迭代”写成 `A` 的连续/可测函数，需要一个
   有限分支 + 零填充的表示（例如用 `Fin (n+1) → …` 的部分轨迹），本卡未做。
2. **峰值函数**：D17 的 `tracePeak` 对列表连续，但列表不是 `A` 的连续函数（第 1 条），
   因此 `A ↦ tracePeak (轨迹 A)` 的连续性仍未支付。
3. **后续步的复合**：本卡只给**一步** `pivotSchur` 的像紧；第二步需要把
   `pivotSchur · p q '' K` 再与新域（非零条目条件/零终止分支）相交，
   分支的相对闭/开性与覆盖未证。
4. **上确界达到 / `rho5`**：`sSup GrowthValues`、`1 ≤ rho5Trace ≤ 16`、alpha 最优性
   与达到性都不在本卡。本卡只提供“紧域上连续映射的像紧”这一单步适配。
-/
import Rho5.Shared.PivotSchurContinuity.Continuous

namespace Rho5.PivotSchurContinuity

open Rho5

/-- **卡目标 4（紧域上的像紧）**：任何包含在 `CPDomain p q` 中的紧集，其 Schur 像紧。 -/
theorem isCompact_image_pivotSchur {n : ℕ} (p q : Fin (n + 1))
    {K : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)} (hK : IsCompact K)
    (hKsub : K ⊆ CPDomain p q) :
    IsCompact ((fun A => Rho5.PivotReindex.pivotSchur A p q) '' K) :=
  hK.image_of_continuousOn ((continuousOn_pivotSchur p q).mono hKsub)

/-- **卡目标 4（盒子交域的像紧）**：条目在 `lo`、`hi` 之间的闭盒与 `CPDomain p q` 相交，
其 Schur 像紧。这是后继“按条目界分块”的紧性入口。 -/
theorem isCompact_image_pivotSchur_entryBox_inter {n : ℕ} (p q : Fin (n + 1))
    (lo hi : Fin (n + 1) → Fin (n + 1) → ℝ) :
    IsCompact ((fun A => Rho5.PivotReindex.pivotSchur A p q) ''
      ((Set.Icc lo hi ∩ (CPDomain p q : Set (Fin (n + 1) → Fin (n + 1) → ℝ))) :
        Set (Fin (n + 1) → Fin (n + 1) → ℝ))) :=
  (isCompact_entryBox_inter_CPDomain p q lo hi).image_of_continuousOn
    ((continuousOn_pivotSchur p q).mono Set.inter_subset_right)

end Rho5.PivotSchurContinuity
