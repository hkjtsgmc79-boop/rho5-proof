/-
D23 — 主元选择与 `movePivot` 桥接
==================================

本文件只准备 `Reduce` 需要的三件事，全部复用已有冻结结果，不重新证明：

* `matrixEntryMax_eq_abs_of_isCompletePivot`：一个完整主元位置的绝对条目**就是**
  冻结元素最大范数（上界来自主元谓词，达到性来自 D08
  `abs_entry_le_matrixEntryMax`；这正是 D13 `head_eq_matrixEntryMax` 用到的同一论证，
  这里只按“完整主元位置”而非“轨迹头部”陈述）；
* `exists_isCompletePivot_ne_zero`：非零矩阵 + 一条真实合法轨迹给出一个**非零**完整
  主元位置（D13 `exists_step_of_ne_zero` 的直接读法，不新增存在性假设）；
* `movePivot` 与 D20 `permuteEntries` 的桥：D10 的 `movePivot A p q` 就是
  `permuteEntries A (Equiv.swap 0 p) (Equiv.swap 0 q)`（定义相同），于是
  D20 的 `matrixEntryMax_permuteEntries` 与固定引理 `legalTrace_permute_iff` 可以直接
  用在 `movePivot` 上（值列表不变）。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.FirstPivotDomain.Domain
import Rho5.Shared.TracePermutation
import Rho5.Shared.PivotReindex

namespace Rho5.FirstPivotDomain

open Rho5 Rho5.GrowthModel

/-- **完整主元的绝对条目 = 冻结元素最大范数**。两个方向分别来自主元谓词
（`∀ i j, |A i j| ≤ |A p q|`）与 D08 的达到性引理。 -/
theorem matrixEntryMax_eq_abs_of_isCompletePivot {A : Matrix5} {p q : Fin 5}
    (hmax : Rho5.Pivot.IsCompletePivot A p q) : matrixEntryMax A = |A p q| := by
  refine le_antisymm ?_ (Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax A p q)
  unfold matrixEntryMax
  exact Finset.sup'_le Finset.univ_nonempty _ (fun ij _ => hmax ij.1 ij.2)

/-- **非零矩阵的合法轨迹给出非零完整主元**：直接读 D13 的 `exists_step_of_ne_zero`
（该分解还给出尾轨迹，但本卡只需要主元位置与非零性）。 -/
theorem exists_isCompletePivot_ne_zero {A : Matrix5} (hA : A ≠ 0) {values : List ℝ}
    (htrace : Rho5.CompletePivotPath.LegalTrace A values) :
    ∃ p q : Fin 5, Rho5.Pivot.IsCompletePivot A p q ∧ A p q ≠ 0 := by
  obtain ⟨p, q, _, hmax, hne, -, -⟩ :=
    Rho5.CompletePivotPath.exists_step_of_ne_zero (n := 4) hA htrace
  exact ⟨p, q, hmax, hne⟩

/-- **桥（定义相同）**：D10 的 `movePivot` 就是 D20 的 `permuteEntries` 在
`Equiv.swap 0 p`、`Equiv.swap 0 q` 处。 -/
theorem movePivot_eq_permuteEntries (A : Matrix5) (p q : Fin 5) :
    Rho5.PivotReindex.movePivot A p q =
      Rho5.TracePermutation.permuteEntries A (Equiv.swap 0 p) (Equiv.swap 0 q) := rfl

/-- 移动主元不改变冻结元素最大范数（D20 `matrixEntryMax_permuteEntries`）。 -/
theorem matrixEntryMax_movePivot (A : Matrix5) (p q : Fin 5) :
    matrixEntryMax (Rho5.PivotReindex.movePivot A p q) = matrixEntryMax A := by
  rw [movePivot_eq_permuteEntries, Rho5.TracePermutation.matrixEntryMax_permuteEntries]

/-- 移动主元不改变合法轨迹，**值列表原样保留**（D20 固定引理
`legalTrace_permute_iff`；无 tie-break 假设，两个方向都有）。 -/
theorem legalTrace_movePivot_iff (A : Matrix5) (p q : Fin 5) (values : List ℝ) :
    Rho5.CompletePivotPath.LegalTrace (Rho5.PivotReindex.movePivot A p q) values ↔
      Rho5.CompletePivotPath.LegalTrace A values := by
  rw [movePivot_eq_permuteEntries]
  exact Rho5.TracePermutation.legalTrace_permute_iff A (Equiv.swap 0 p) (Equiv.swap 0 q) values

/-- 移动主元后 `(0, 0)` 就是原主元值（D10 `movePivot_zero_zero` 的桥接形式）。 -/
theorem movePivot_zero_zero_eq (A : Matrix5) (p q : Fin 5) :
    Rho5.PivotReindex.movePivot A p q 0 0 = A p q :=
  Rho5.PivotReindex.movePivot_zero_zero A p q

/-- 移动后 `(0, 0)` 是完整主元（D10 `isCompletePivot_movePivot_iff`）。 -/
theorem isCompletePivot_movePivot_zero_zero_iff (A : Matrix5) (p q : Fin 5) :
    Rho5.Pivot.IsCompletePivot (Rho5.PivotReindex.movePivot A p q) 0 0 ↔
      Rho5.Pivot.IsCompletePivot A p q :=
  Rho5.PivotReindex.isCompletePivot_movePivot_iff A p q

end Rho5.FirstPivotDomain
