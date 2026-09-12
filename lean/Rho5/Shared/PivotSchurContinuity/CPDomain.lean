/-
D32 — 合法主元域 `CPDomain`
============================

**卡目标 1.** 对任意 `n` 与 `p q : Fin (n+1)`，在**实际**
`Matrix (Fin (n+1)) (Fin (n+1)) ℝ` 上定义合法主元域

  `CPDomain p q = {A | IsCompletePivot A p q}`

并证明：

* 它是**闭集**（主元谓词是 25/`(n+1)²` 个非严格不等式 `|A i j| ≤ |A p q|` 的交，
  每个都是连续函数的闭水平集，故任意交闭——不需要有限性假设也成立，这里用
  `isClosed_iInter` + `isClosed_le`）；
* 它**包含零**（`|0| ≤ |0|`）；
* **零主元且合法 ⇒ 整个 `A = 0`**（D10 的
  `eq_zero_of_isCompletePivot_of_pivot_eq_zero`，本卡原样引用，不重证）；
* 以及后续要用的两个零件：条目求值的连续性 `continuous_matrix_entry`（一般 `m n`，
  与 D26 的 `Fin 5` 专用引理不重名也不重复其“第一步多项式连续性”），
  零矩阵的 `pivotSchur` 为零 `pivotSchur_zero`。

拓扑：**引用 D26 已声明的实矩阵乘积拓扑实例**
`Rho5.FirstPivotCompact.instTopologicalSpaceMatrix`（`Matrix m n ℝ` 上等于
`Pi.topologicalSpace`）；本卡不重复声明相同实例、不改 `Matrix` 可约性。
序结构（盒子的 `Set.Icc`）写在坐标空间 `Fin (n+1) → Fin (n+1) → ℝ` 上，
mathlib 的 Pi 实例直接给出 `Preorder`/`OrderClosedTopology`/`CompactIccSpace`。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Rho5.Shared.FirstPivotCompact.Domain
import Rho5.Shared.PivotReindex

namespace Rho5.PivotSchurContinuity

open Rho5

/-- **卡目标 1（域定义）**：`(p, q)` 是完整主元的矩阵集合。谓词是 pilot 冻结的
`Rho5.Pivot.IsCompletePivot`，本卡不重新定义。 -/
def CPDomain {n : ℕ} (p q : Fin (n + 1)) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
  {A | Rho5.Pivot.IsCompletePivot A p q}

/-- 成员展开：`A ∈ CPDomain p q ↔ ∀ i j, |A i j| ≤ |A p q|`。 -/
theorem mem_CPDomain_iff {n : ℕ} {p q : Fin (n + 1)}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} :
    A ∈ CPDomain p q ↔ Rho5.Pivot.IsCompletePivot A p q :=
  Iff.rfl

/-- **卡目标 1（含零）**：零矩阵的每个条目满足 `|0| ≤ |0|`，故 `0 ∈ CPDomain p q`。 -/
theorem zero_mem_CPDomain {n : ℕ} (p q : Fin (n + 1)) :
    (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) ∈ CPDomain p q := by
  intro i j
  simp

/-- **卡目标 1（零主元 ⇒ 零矩阵）**：合法主元若取值为零，则整个矩阵为零。
这是 D10 的 `eq_zero_of_isCompletePivot_of_pivot_eq_zero` 在域成员上的读法。 -/
theorem eq_zero_of_mem_CPDomain_of_pivot_eq_zero {n : ℕ} {p q : Fin (n + 1)}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A ∈ CPDomain p q) (hpq : A p q = 0) :
    A = 0 :=
  Rho5.PivotReindex.eq_zero_of_isCompletePivot_of_pivot_eq_zero A p q hA hpq

/-- 条目求值的连续性（`Matrix m n ℝ` 的乘积拓扑由 D26 的实例给出）。 -/
theorem continuous_matrix_entry {m n : Type*} (i : m) (j : n) :
    Continuous (fun A : Matrix m n ℝ => A i j) :=
  (continuous_apply j).comp (continuous_apply i)

/-- **卡目标 1（闭性）**：`CPDomain p q` 是全部条目不等式
`|A i j| ≤ |A p q|` 的交，每个都是连续函数的闭水平集，故闭。 -/
theorem isClosed_CPDomain {n : ℕ} (p q : Fin (n + 1)) : IsClosed (CPDomain p q) := by
  have h : CPDomain p q
      = ⋂ i, ⋂ j, {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ | |A i j| ≤ |A p q|} := by
    ext A
    simp only [CPDomain, Set.mem_setOf_eq, Set.mem_iInter, Rho5.Pivot.IsCompletePivot]
  rw [h]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_le (continuous_matrix_entry i j).abs (continuous_matrix_entry p q).abs

/-- 零矩阵的 `pivotSchur` 是零矩阵（`0 - 0 * 0 / 0 = 0`，实数全除法下也成立）。 -/
theorem pivotSchur_zero {n : ℕ} (p q : Fin (n + 1)) :
    Rho5.PivotReindex.pivotSchur (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) p q = 0 := by
  ext i j
  rw [Rho5.PivotReindex.pivotSchur_apply]
  simp

/-- **卡目标 4 的紧域零件**：给定条目上下界 `lo hi`，坐标空间中的闭盒子
`Set.Icc lo hi` 与 `CPDomain p q` 的交紧（闭盒子的闭子集）。 -/
theorem isCompact_entryBox_inter_CPDomain {n : ℕ} (p q : Fin (n + 1))
    (lo hi : Fin (n + 1) → Fin (n + 1) → ℝ) :
    IsCompact (Set.Icc lo hi ∩ (CPDomain p q : Set (Fin (n + 1) → Fin (n + 1) → ℝ))) :=
  (isCompact_Icc (a := lo) (b := hi)).of_isClosed_subset
    (isClosed_Icc.inter (isClosed_CPDomain p q)) Set.inter_subset_left

end Rho5.PivotSchurContinuity
