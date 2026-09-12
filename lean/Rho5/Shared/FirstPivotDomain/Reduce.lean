/-
D23 — 约化：任意真实增长值都由首主元 `+1` 域中的矩阵实现
=========================================================

**卡目标 2.** 对任何非零 `A` 与**真实**合法轨迹 `values`，本文件构造一个 `Matrix5 B`
与一条真实合法轨迹 `ws`，使

  `matrixEntryMax B = 1`，`B 0 0 = 1`，`IsCompletePivot B 0 0`，
  `LegalTrace B ws`，且 `growthRatio B ws = growthRatio A values`。

构造（每一步都复用已有冻结结果，不重新证明）：

1. 由 D13 `exists_step_of_ne_zero` 取一个**非零**完整主元位置 `(p, q)`（`A p q ≠ 0`）；
2. 用 D10 `movePivot A p q`（即 D20 `permuteEntries` 在 `Equiv.swap 0 p`、`Equiv.swap 0 q`）
   把该主元搬到 `(0, 0)`：`(movePivot A p q) 0 0 = A p q`，轨迹列表原样运输
   （D20 固定引理），元素最大范数不变；
3. 用该主元的**非零实数倒数** `(A p q)⁻¹` 整体缩放：`B := (A p q)⁻¹ • movePivot A p q`。
   因为完整主元的绝对条目就是元素最大范数（`matrixEntryMax_eq_abs_of_isCompletePivot`），
   `matrixEntryMax B = |(A p q)⁻¹| * |A p q| = 1`，且 `B 0 0 = (A p q)⁻¹ * A p q = 1`。
   主元为负时 `(A p q)⁻¹` 也是负的，但元素最大范数与峰值都用 `|·|`，所以没有符号分支遗漏；
4. 轨迹按的**整条缩放**规则变为 `ws := values.map (fun v => |(A p q)⁻¹| * v)`
   （D13 `legalTrace_smul`，含负标量情形），**不是**原列表；
5. 增长比不变：D17 `growthRatio_smul` 给出
   `growthRatio B ws = growthRatio (movePivot A p q) values`，移动主元不改变峰值与
   元素最大范数，故再等于 `growthRatio A values`。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.FirstPivotDomain.PivotEntry

namespace Rho5.FirstPivotDomain

open Rho5 Rho5.GrowthModel

/-- **卡目标 2（约化定理）**：非零矩阵的任何真实合法轨迹增长比，都由一个
“元素最大范数 `1`、首主元 `+1`、`(0, 0)` 是完整主元”的矩阵的一条真实合法轨迹实现。

证明显式使用 `(A p q)⁻¹` 的绝对值作为缩放因子，因此**原主元为负时同样正确**；
轨迹是整条按 `|(A p q)⁻¹|` 缩放的列表，不是原列表。 -/
theorem exists_firstPivot_reduction {A : Matrix5} (hA : A ≠ 0) {values : List ℝ}
    (htrace : Rho5.CompletePivotPath.LegalTrace A values) :
    ∃ (B : Matrix5) (ws : List ℝ),
      matrixEntryMax B = 1 ∧ B 0 0 = 1 ∧ Rho5.Pivot.IsCompletePivot B 0 0 ∧
        Rho5.CompletePivotPath.LegalTrace B ws ∧ growthRatio B ws = growthRatio A values := by
  obtain ⟨p, q, hmax, hne⟩ := exists_isCompletePivot_ne_zero hA htrace
  have hc : (A p q)⁻¹ ≠ 0 := inv_ne_zero hne
  have htrace' : Rho5.CompletePivotPath.LegalTrace (Rho5.PivotReindex.movePivot A p q) values :=
    (legalTrace_movePivot_iff A p q values).mpr htrace
  refine ⟨(A p q)⁻¹ • Rho5.PivotReindex.movePivot A p q,
    values.map (fun v => |(A p q)⁻¹| * v), ?_, ?_, ?_, ?_, ?_⟩
  · -- 元素最大范数 = 1
    rw [Rho5.MatrixNormalization.matrixEntryMax_smul, matrixEntryMax_movePivot,
      matrixEntryMax_eq_abs_of_isCompletePivot hmax, abs_inv,
      inv_mul_cancel₀ (abs_ne_zero.mpr hne)]
  · -- 首主元 = 1（原主元可为负，倒数仍把 A p q 变成 1）
    rw [Rho5.MatrixNormalization.smul_apply_entry, movePivot_zero_zero_eq, inv_mul_cancel₀ hne]
  · -- (0, 0) 是完整主元
    exact (Rho5.MatrixNormalization.isCompletePivot_smul_iff
      (Rho5.PivotReindex.movePivot A p q) 0 0 hc).mpr
      ((isCompletePivot_movePivot_zero_zero_iff A p q).mpr hmax)
  · -- 整条轨迹按 |·| 缩放后仍合法
    exact Rho5.CompletePivotPath.legalTrace_smul (A p q)⁻¹ hc htrace'
  · -- 增长比不变（先缩放不变，再搬主元不变）
    calc growthRatio ((A p q)⁻¹ • Rho5.PivotReindex.movePivot A p q)
          (values.map (fun v => |(A p q)⁻¹| * v))
        = growthRatio (Rho5.PivotReindex.movePivot A p q) values :=
          growthRatio_smul _ hc values
      _ = growthRatio A values := by
          rw [growthRatio_eq, growthRatio_eq, matrixEntryMax_movePivot]

/-- 卡目标 2 的“域版本”：任何真实增长值都在首主元域中。 -/
theorem growthValue_mem_firstPivotGrowthValues {A : Matrix5} (hA : A ≠ 0) {values : List ℝ}
    (htrace : Rho5.CompletePivotPath.LegalTrace A values) :
    growthRatio A values ∈ FirstPivotGrowthValues := by
  obtain ⟨B, ws, hmax, h00, hpiv, htraceB, hgr⟩ := exists_firstPivot_reduction hA htrace
  exact ⟨B, ws, hmax, h00, hpiv, htraceB, hgr.symm⟩

end Rho5.FirstPivotDomain
