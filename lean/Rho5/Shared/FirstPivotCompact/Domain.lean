/-
D26 — 首主元 `+1` 矩阵域 `K`
=============================

**卡目标 1.** 用**实际** `Rho5.Matrix5` 定义首主元矩阵域

  `K = {A | matrixEntryMax A = 1 ∧ A 0 0 = 1 ∧ IsCompletePivot A 0 0}`

并证明它与坐标刻画 `{A | A 0 0 = 1 ∧ ∀ i j, |A i j| ≤ 1}` 相等。两个方向都只引用已有结果：

* `→`：`A 0 0 = 1` 直接取出；每个条目由 D08 `abs_entry_le_matrixEntryMax` 与
  `matrixEntryMax A = 1` 夹住，**不需要**主元谓词；
* `←`：`matrixEntryMax A = 1` 由 D08 的 `Finset.sup'_le`（上界）与
  `abs_entry_le_matrixEntryMax`（达到性）两侧夹出；`IsCompletePivot A 0 0` 即
  `∀ i j, |A i j| ≤ |A 0 0| = 1`，也就是假设本身。

**乘积拓扑桥实例（本卡唯一的实例声明）.** mathlib 的 `Matrix m n ℝ` 是半可约 `def`
（`m → n → ℝ`），实例搜索**不会**展开它，因此 `TopologicalSpace (Matrix m n ℝ)`、
`Preorder`、`CompactIccSpace` 等都不自动可用。本卡显式声明

  `instTopologicalSpaceMatrix : TopologicalSpace (Matrix m n ℝ) := Pi.topologicalSpace`

即坐标空间上的**同一个**乘积拓扑（`instTopologicalSpaceMatrix_eq` 用 `rfl` 记录这一点），
而不是第二套拓扑，也不是拿别的数组类型顶替矩阵：后续所有拓扑/紧性陈述仍然写在
`Matrix5` 与其坐标空间上。序结构不需要新实例——盒子的 25 个闭区间写在坐标空间
`Fin 5 → Fin 5 → ℝ` 上（`firstPivotBox`），`Preorder`/`OrderClosedTopology`/`CompactIccSpace`
在那里由 mathlib 的 Pi 实例直接给出（探针已验证）。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Constructions
import Rho5.Shared.FirstPivotDomain.Domain
import Rho5.Shared.PivotReindex

namespace Rho5.FirstPivotCompact

open Rho5

/-! ## 乘积拓扑桥 -/

/-- **桥实例**：实矩阵上的乘积拓扑，与坐标空间 `m → n → ℝ` 的 Pi 拓扑**定义相同**。
声明它的唯一原因是 mathlib 的 `Matrix` 是半可约 `def`，实例搜索不展开它。 -/
instance instTopologicalSpaceMatrix {m n : Type*} : TopologicalSpace (Matrix m n ℝ) :=
  Pi.topologicalSpace

/-- 桥实例的识别引理：它与 `Pi.topologicalSpace` 逐字相同（`rfl`），因此没有引入第二套拓扑。 -/
theorem instTopologicalSpaceMatrix_eq {m n : Type*} :
    (inferInstance : TopologicalSpace (Matrix m n ℝ)) = Pi.topologicalSpace := rfl

/-- 条目求值的连续性（Pi 投影的两次复合）。 -/
theorem continuous_entry (i j : Fin 5) : Continuous (fun A : Matrix5 => A i j) :=
  (continuous_apply j).comp (continuous_apply i)

/-! ## 域与盒子 -/

/-- **卡目标 1（首主元矩阵域）**：元素最大范数为 `1`、首主元恰为 `+1`、且 `(0, 0)`
是完整主元的**实际** `Matrix5`。冻结语义全部原样复用（D08 的 `matrixEntryMax`、
pilot 的 `IsCompletePivot`），没有第二套范数或主元谓词。 -/
def firstPivotDomain : Set Matrix5 :=
  {A | matrixEntryMax A = 1 ∧ A 0 0 = 1 ∧ Rho5.Pivot.IsCompletePivot A 0 0}

/-- 25 个坐标的闭区间盒子（写在坐标空间上，序结构由 mathlib 的 Pi 实例给出）。 -/
def firstPivotBox : Set (Fin 5 → Fin 5 → ℝ) :=
  Set.Icc (fun _ _ : Fin 5 => (-1 : ℝ)) (fun _ _ => 1)

/-- **卡目标 1（等价刻画）**：`A ∈ K` 当且仅当 `A 0 0 = 1` 且全部 25 个条目的绝对值 ≤ 1。 -/
theorem mem_firstPivotDomain_iff {A : Matrix5} :
    A ∈ firstPivotDomain ↔ A 0 0 = 1 ∧ ∀ i j, |A i j| ≤ 1 := by
  constructor
  · rintro ⟨hmax, h00, -⟩
    exact ⟨h00, fun i j => by
      rw [← hmax]
      exact Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax A i j⟩
  · rintro ⟨h00, hbound⟩
    refine ⟨?_, h00, ?_⟩
    · refine le_antisymm ?_ ?_
      · unfold matrixEntryMax
        exact Finset.sup'_le Finset.univ_nonempty _ (fun ij _ => hbound ij.1 ij.2)
      · have h := Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax A 0 0
        rw [h00] at h
        simpa using h
    · intro i j
      rw [h00]
      simpa using hbound i j

/-- 盒子的成员刻画：`A ∈ box ↔ ∀ i j, |A i j| ≤ 1`（`abs_le` 与 `Set.Icc` 的逐坐标展开）。 -/
theorem mem_firstPivotBox_iff {A : Fin 5 → Fin 5 → ℝ} :
    A ∈ firstPivotBox ↔ ∀ i j, |A i j| ≤ 1 := by
  unfold firstPivotBox
  simp only [Set.mem_Icc, Pi.le_def, abs_le]
  exact ⟨fun h i j => ⟨h.1 i j, h.2 i j⟩, fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩⟩

/-- **卡目标 1（集合等式）**：`K` 就是 25 个坐标的闭区间盒子与坐标等式 `A 0 0 = 1` 的交
（在坐标空间中表述；与 `Set Matrix5` 定义相同）。 -/
theorem firstPivotDomain_eq_box_inter :
    (firstPivotDomain : Set (Fin 5 → Fin 5 → ℝ)) = firstPivotBox ∩ {A | A 0 0 = 1} := by
  ext A
  constructor
  · intro hA
    have h := mem_firstPivotDomain_iff.mp hA
    exact ⟨mem_firstPivotBox_iff.mpr h.2, h.1⟩
  · intro hA
    obtain ⟨hbox, h00⟩ := hA
    exact mem_firstPivotDomain_iff.mpr ⟨h00, mem_firstPivotBox_iff.mp hbox⟩

/-- 域非空：常值 `1` 矩阵在 `K` 中（元素最大范数引理复用 D17/D23 的
`matrixEntryMax_const_one`；主元谓词在 `|1| ≤ |1|` 处成立）。 -/
theorem firstPivotDomain_nonempty : firstPivotDomain.Nonempty :=
  ⟨fun _ _ => 1, by
    refine ⟨Rho5.GrowthModel.matrixEntryMax_const_one, rfl, ?_⟩
    intro i j
    simp⟩

end Rho5.FirstPivotCompact
